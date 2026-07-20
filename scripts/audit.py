#!/usr/bin/env python3
"""Meno review audit (introduced at review #28, Phase 64).

Machine-assists four review obligations:

1. CITATIONS   — every backticked identifier in README.md names something
                 real in Meno/ (a declaration, or at least a source token:
                 structure fields and file names resolve at the token tier).
2. DELETIONS   — no name recorded deleted in scripts/deleted.txt is
                 declared anywhere in Meno/ (deletions stay deleted).
3. ARCHITECTURE— README's architecture block lists exactly the files of
                 Meno/, and Meno.lean imports exactly those files.
4. REACHABILITY— every named declaration outside Completion.lean is
                 transitively reachable from a README-cited result, or is
                 an instance / attribute-tagged lemma (consumed by
                 elaboration, not by name — reported, not failed), and
                 every certificate field assignment targets a model-live
                 declaration (a certificate field is not a consumer —
                 Phase 61 rule).

The reachability graph is textual and conservative: comments and
docstrings are stripped before tokenizing (a docstring mention is not a
reader), dotted tokens match by qualified suffix, projection notation
and open-namespace references match by component. Conservative means it
over-links (keeps things live) rather than under-links; unreachability
findings are candidates for review, and the exit code treats any
non-instance unreachable declaration as a failure.

Exit code 0 = all four legs pass.
"""

import re
import sys
from pathlib import Path
from collections import defaultdict, deque

REPO = Path(__file__).resolve().parent.parent
MENO = REPO / "Meno"
README = REPO / "README.md"
CERT = "Completion.lean"

DECL_KEYWORDS = ("theorem", "lemma", "def", "abbrev", "structure",
                 "class", "inductive", "instance", "opaque")
MODIFIERS = ("private", "protected", "noncomputable", "scoped",
             "unsafe", "partial", "nonrec")

# ---------------------------------------------------------------- strip

def strip_comments(text):
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        c = text[i]
        if depth == 0:
            out.append(c)
        elif c == "\n":
            out.append("\n")
        i += 1
    return "".join(out)

# ---------------------------------------------------------------- parse

NAME_RE = r"[A-Za-z_À-ʯͰ-Ͽ℀-⅏][A-Za-z0-9_'₀-₉À-ʯͰ-Ͽ℀-⅏!?\.]*"
decl_line_re = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:" + "|".join(MODIFIERS) + r")\s+)*"
    r"(" + "|".join(DECL_KEYWORDS) + r")\b(?:\s+(" + NAME_RE + r"))?")
ns_re = re.compile(r"^\s*namespace\s+(" + NAME_RE + r")\s*$")
sec_re = re.compile(r"^\s*section(?:\s+(" + NAME_RE + r"))?\s*$")
end_re = re.compile(r"^\s*end(?:\s+(" + NAME_RE + r"))?\s*$")
token_re = re.compile(NAME_RE)

class Decl:
    def __init__(self, kind, full, file, line):
        self.kind, self.full, self.file, self.line = kind, full, file, line
        self.span, self.attrs = [], ""

def parse_file(path):
    lines = strip_comments(path.read_text()).split("\n")
    decls, stack, current, pending = [], [], None, ""
    for lineno, line in enumerate(lines, 1):
        if ns_re.match(line):
            for part in ns_re.match(line).group(1).split("."):
                stack.append(("ns", part))
        elif sec_re.match(line):
            stack.append(("sec", sec_re.match(line).group(1)))
        elif end_re.match(line):
            label = end_re.match(line).group(1)
            for _ in (label.split(".") if label else [None]):
                if stack: stack.pop()
        else:
            m = decl_line_re.match(line)
            if m:
                kind, name = m.group(1), m.group(2)
                ns = [n for (k, n) in stack if k == "ns"]
                full = ".".join(ns + [name]) if name not in (None, ":", ":=") else None
                current = Decl(kind, full, path.name, lineno)
                current.attrs = pending + " " + line
                pending = ""
                current.span.append(line)
                decls.append(current)
                continue
            if line.lstrip().startswith("@["):
                pending += " " + line
        if current is not None:
            current.span.append(line)
    return decls

# ---------------------------------------------------------------- match

def variable_like(s):
    return len(s) <= 2 or s[0].islower()

def build_index(decls):
    by_last, by_full = defaultdict(list), {}
    for d in decls:
        if d.full:
            by_full[d.full] = d
            by_last[d.full.split(".")[-1]].append(d)
    return by_full, by_last

def suffix_hits(token, by_last):
    return {d for d in by_last.get(token.split(".")[-1], [])
            if d.full == token or d.full.endswith("." + token)}

def resolve(token, by_full, by_last):
    token = token.rstrip(".")
    hits = set()
    if token in by_full:
        hits.add(by_full[token])
    if "." in token:
        hits |= suffix_hits(token, by_last)
        if hits:
            return hits
        parts = token.split(".")
        for k in range(len(parts) - 1, 0, -1):
            h = suffix_hits(".".join(parts[:k]), by_last)
            if h:
                hits |= h
                break
        if variable_like(parts[0]):
            for comp in parts[1:]:
                hits.update(by_last.get(comp, []))
        return hits
    hits.update(by_last.get(token, []))
    return hits

# ---------------------------------------------------------------- legs

def main():
    ok = True
    all_decls = []
    for f in sorted(MENO.glob("*.lean")):
        all_decls.extend(parse_file(f))
    model = [d for d in all_decls if d.file != CERT]
    by_full, by_last = build_index(model)
    cert_by_full, cert_by_last = build_index(all_decls)
    readme = README.read_text()
    raw_tree = "\n".join(f.read_text() for f in sorted(MENO.glob("*.lean")))

    # -- 1. citations
    cited = sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_.'₀-₉]*)`", readme)))
    bad = [c for c in cited
           if not resolve(c, cert_by_full, cert_by_last)
           and not re.search(r"\b" + re.escape(c.split(".")[-1]) + r"\b", raw_tree)]
    print(f"[citations]    {len(cited)} identifiers cited; unresolved: {len(bad)}")
    for c in bad:
        print(f"  UNRESOLVED: {c}")
    ok &= not bad

    # -- 2. deletions stay deleted
    deny = set()
    deleted_file = REPO / "scripts" / "deleted.txt"
    for line in deleted_file.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            deny.add(line)
    redecl = [d.full for d in all_decls if d.full and (
        d.full in deny or any(d.full.endswith("." + n) or n == d.full for n in deny))]
    print(f"[deletions]    {len(deny)} recorded names; re-declared: {len(redecl)}")
    for n in redecl:
        print(f"  RE-DECLARED: {n}")
    ok &= not redecl

    # -- 3. architecture
    tree_files = sorted(p.name for p in MENO.glob("*.lean"))
    arch_files = sorted(set(re.findall(r"([A-Za-z][A-Za-z0-9]*\.lean)",
                       readme[readme.find("## Architecture"):readme.find("## Reading")])))
    imports = sorted(set(re.findall(r"^import Meno\.([A-Za-z0-9]+)$",
                       (REPO / "Meno.lean").read_text(), re.M)))
    import_files = sorted(i + ".lean" for i in imports)
    d1 = set(tree_files) ^ set(arch_files)
    d2 = set(tree_files) ^ set(import_files)
    print(f"[architecture] tree {len(tree_files)} files; README-block mismatch: {sorted(d1)}; import mismatch: {sorted(d2)}")
    ok &= not d1 and not d2

    # -- 4. reachability
    roots = set()
    for c in cited:
        roots |= resolve(c, by_full, by_last)
    roots |= {d for d in model if d.full is None}      # anonymous instances
    edges = defaultdict(set)
    for d in model:
        text = "\n".join(d.span)
        for tok in token_re.findall(text):
            for t in resolve(tok, by_full, by_last):
                if t is not d:
                    edges[d].add(t)
    live, queue = set(), deque(roots)
    while queue:
        d = queue.popleft()
        if d in live: continue
        live.add(d)
        queue.extend(t for t in edges[d] if t not in live)
    attr = {d for d in model if re.search(
        r"@\[[^\]]*\b(simp|ext|fun_prop|norm_cast|push_cast)\b", d.attrs)}
    named = [d for d in model if d.full]
    dead = [d for d in named if d not in live]
    dead_hard = [d for d in dead if d.kind != "instance" and d not in attr]
    dead_elab = [d for d in dead if d not in dead_hard]
    print(f"[reachability] {len(named)} named decls; live {len([d for d in named if d in live])}; "
          f"elaboration-retained {len(dead_elab)}; UNREACHABLE {len(dead_hard)}")
    for d in sorted(dead_hard, key=lambda d: (d.file, d.line)):
        print(f"  UNREACHABLE: {d.file}:{d.line} {d.full}")
    ok &= not dead_hard

    # certificate assignment targets must be model-live
    cert_text = strip_comments((MENO / CERT).read_text())
    targets = set(re.findall(r":=\s*⟨?\s*(" + NAME_RE + r")", cert_text))
    bad_t = []
    for t in sorted(targets):
        hits = resolve(t, by_full, by_last)
        if hits and not any(h in live for h in hits):
            bad_t.append(t)
    print(f"[certificate]  assignment targets not model-live: {len(bad_t)}")
    for t in bad_t:
        print(f"  CERT-ONLY: {t}")
    ok &= not bad_t

    print("AUDIT " + ("PASS" if ok else "FAIL"))
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
