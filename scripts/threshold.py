#!/usr/bin/env python3
# /// script
# requires-python = ">=3.12"
# dependencies = ["numpy"]
# ///
"""Logical entropy and ML failure on the L×L torus under i.i.d. edge noise.

The 2-complex is the square torus: vertices Z_L², an edge to the right and
an edge down from each vertex, a face per square. Errors are ZMod 2
1-cochains, each edge flipped independently with probability p; the gauge
is the image of the vertex gradient; the syndrome is the face coboundary.
H¹ = (Z/2)², so each syndrome fiber holds four classes, and the logical
dichotomy (`logicalEntropy_pos_iff`) makes both quantities positive at
every L and p > 0. The threshold is how they scale with L.

For a sampled error e, the posterior over the four classes e + h given
the syndrome is Z(e + h) / Σ Z, where Z(c) = Σ_g P(c + δg) sums the
class's mass over the gauge — the random-bond Ising partition function on
the Nishimori line, computed exactly by a row transfer matrix. Then

    logicalEntropy = E_e[ H(posterior) ]        (nats, as in Lean)
    ML failure     = E_e[ 1 − max posterior ]   (1 − successProb mlRule)

are unbiased Monte Carlo estimates. `--exact` checks them at L = 3
against full enumeration of all 2^18 errors.
"""

import argparse
import math
from concurrent.futures import ProcessPoolExecutor

import numpy as np


def edge_weights(p):
    return np.array([1.0 - p, p])


def log_class_mass(ch, cv, p):
    """log Z for the class of the error with horizontal bits ch[r, j]
    (edge (r,j)–(r,j+1)) and vertical bits cv[r, j] (edge (r,j)–(r+1,j)),
    up to a class-independent constant."""
    L = ch.shape[0]
    w = edge_weights(p)
    n = 1 << L
    bits = (np.arange(n)[:, None] >> np.arange(L)[None, :]) & 1
    nxt = np.roll(bits, -1, axis=1)

    def diag(r):
        return np.prod(w[bits ^ nxt ^ ch[r][None, :]], axis=1)

    M = np.diag(diag(0))
    logscale = 0.0
    for r in range(L):
        T = M.reshape((n,) + (2,) * L)
        for j in range(L):
            k = w[np.array([[cv[r, j], 1 - cv[r, j]], [1 - cv[r, j], cv[r, j]]])]
            # bit j of the state index is axis (L - j) of the reshaped tensor
            ax = L - j
            T = np.moveaxis(np.tensordot(T, k, axes=([ax], [0])), -1, ax)
        M = T.reshape(n, n)
        if r + 1 < L:
            M = M * diag(r + 1)[None, :]
        s = M.max()
        M = M / s
        logscale += math.log(s)
    return logscale + math.log(np.trace(M))


def logicals(L):
    """Representatives of the nonzero part of H¹: a ring of vertical
    edges and a ring of horizontal edges, each a non-exact cocycle."""
    z = np.zeros((L, L), dtype=np.int64)
    a = (z.copy(), z.copy())
    a[1][0, :] = 1
    b = (z.copy(), z.copy())
    b[0][:, 0] = 1
    return [(z, z), a, b, (a[0] ^ b[0], a[1] ^ b[1])]


def posterior(ch, cv, p, reps):
    logs = np.array([log_class_mass(ch ^ hh, cv ^ hv, p) for hh, hv in reps])
    q = np.exp(logs - logs.max())
    return q / q.sum()


def entropy(q):
    q = q[q > 0]
    return float(-(q * np.log(q)).sum())


def estimate(L, p, n, rng):
    if not isinstance(rng, np.random.Generator):
        rng = np.random.default_rng(rng)
    reps = logicals(L)
    hs, fs = np.empty(n), np.empty(n)
    for i in range(n):
        ch = (rng.random((L, L)) < p).astype(np.int64)
        cv = (rng.random((L, L)) < p).astype(np.int64)
        q = posterior(ch, cv, p, reps)
        hs[i], fs[i] = entropy(q), 1.0 - q.max()
    se = lambda x: x.std(ddof=1) / math.sqrt(n)
    return hs.mean(), se(hs), fs.mean(), se(fs)


def exact_L3(p):
    """Full enumeration at L = 3: logical entropy = H(σ, w) − H(σ) and ML
    success = Σ_σ max_w P(σ, w), with w the pairing against the two
    homology cycles (which separates the classes in a syndrome fiber)."""
    L = 3
    E = 2 * L * L
    errs = np.arange(1 << E, dtype=np.int64)
    bit = lambda k: (errs >> k) & 1
    hidx = lambda r, j: r * L + j
    vidx = lambda r, j: L * L + r * L + j
    syn = np.zeros_like(errs)
    for r in range(L):
        for j in range(L):
            f = (
                bit(hidx(r, j))
                ^ bit(hidx((r + 1) % L, j))
                ^ bit(vidx(r, j))
                ^ bit(vidx(r, (j + 1) % L))
            )
            syn |= f << (r * L + j)
    wr = np.zeros_like(errs)
    wc = np.zeros_like(errs)
    for j in range(L):
        wr ^= bit(hidx(0, j))
    for r in range(L):
        wc ^= bit(vidx(r, 0))
    wt = np.zeros_like(errs)
    for k in range(E):
        wt += bit(k)
    mass = p**wt * (1 - p) ** (E - wt)
    joint = np.zeros((1 << (L * L), 4))
    np.add.at(joint, (syn, wr * 2 + wc), mass)
    js = joint.sum(axis=1)
    H = lambda x: float(-(x[x > 0] * np.log(x[x > 0])).sum())
    fibers = (
        int((joint > 0).sum(axis=1).max()),
        int((joint > 0).sum(axis=1)[js > 0].min()),
    )
    return H(joint.ravel()) - H(js), 1.0 - joint.max(axis=1).sum(), fibers


def crossing(ps, a, b):
    d = np.asarray(a) - np.asarray(b)
    for k in range(len(ps) - 1):
        if d[k] < 0 <= d[k + 1]:
            t = -d[k] / (d[k + 1] - d[k])
            return ps[k] + t * (ps[k + 1] - ps[k])
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--sizes", type=int, nargs="+", default=[4, 5, 6, 7, 8])
    ap.add_argument(
        "--ps",
        type=float,
        nargs="+",
        default=[0.06, 0.08, 0.09, 0.10, 0.105, 0.11, 0.115, 0.12, 0.14],
    )
    ap.add_argument("--samples", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument(
        "--exact", action="store_true", help="check L = 3 against enumeration"
    )
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)

    if args.exact:
        print("L = 3: enumeration vs transfer-matrix Monte Carlo")
        for p in (0.05, 0.1, 0.2):
            h, f, (fmax, fmin) = exact_L3(p)
            hm, hse, fm, fse = estimate(3, p, args.samples, rng)
            print(
                f"  p={p:.2f}  H_log exact {h:.5f}  MC {hm:.5f}±{hse:.5f}"
                f"   fail exact {f:.5f}  MC {fm:.5f}±{fse:.5f}"
                f"   classes per fiber {fmin}..{fmax}"
            )
        return

    jobs = [(L, p) for L in args.sizes for p in args.ps]
    seeds = np.random.SeedSequence(args.seed).spawn(len(jobs))
    with ProcessPoolExecutor() as ex:
        out = ex.map(estimate, *zip(*jobs), [args.samples] * len(jobs), seeds)
        flat = dict(zip(jobs, out))
    res = {L: [flat[L, p] for p in args.ps] for L in args.sizes}
    for name, k in (("logical entropy (nats)", 0), ("ML failure", 2)):
        print(f"\n{name}")
        print("    p  " + "".join(f"        L={L:<6}" for L in args.sizes))
        for i, p in enumerate(args.ps):
            row = "".join(
                f"  {res[L][i][k]:.4f}±{res[L][i][k + 1]:.4f}" for L in args.sizes
            )
            print(f"  {p:.3f}{row}")
        pairs = list(zip(args.sizes, args.sizes[1:])) + list(
            zip(args.sizes, args.sizes[2:])
        )
        for L1, L2 in pairs:
            c = crossing(args.ps, [r[k] for r in res[L2]], [r[k] for r in res[L1]])
            print(
                f"  crossing L={L1}/{L2}: " + (f"p ≈ {c:.4f}" if c else "none in range")
            )


if __name__ == "__main__":
    main()
