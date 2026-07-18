/-! # The documentation acceptance check (PLAN, C12)

`lake exe check`, run from the **repository root** — the directory
holding `lakefile.toml`. Lake itself refuses to start anywhere else,
so the check does not pretend to search for the root: it verifies the
working directory and fails closed. Requires exactly one Part II
marker in `PLAN.md`, and sweeps PLAN Part I, `README.md`, `Meno.lean`,
and every `.lean` file under `Meno/` — recursively — for retired
identifiers and deleted paths. Any missing file or I/O error exits
nonzero. In the Lean toolchain, not a shell script (review #8 and
maintainer preference). -/

def blacklist : List String :=
  [ "CycleBasis", "CyclePresentation", "IntegralCyclePresentation"
  , "PeriodLattice.lean", "FundamentalPresentation", "fundamentalPresentation"
  , "r_eq_b1", "exists_rebase_related", "rebase_energy", "rebase_partFn"
  , "rebaseEquiv", "toGramData", "killed_releases_mass"
  , "TransitionComplexity", "HomKernel", "TypeKernel", "staleness banner"
  , "of_posDef", "finPrefixSum", "wedgePotential", "thetaCycleBasis"
  , "thetaIntegralPresentation", "cycleIntegralPresentation"
  , "wedgeGraphIntegralPresentation", "gramOf_fund", "fundCyclesZ_mem" ]

def partIIMarker : String := "# Part II"

def containsSub (hay pat : String) : Bool :=
  ((hay.splitOn pat).length > 1)

def sweep (label : String) (text : String) : List String :=
  (text.splitOn "\n").zipIdx.flatMap fun (line, i) =>
    blacklist.filterMap fun pat =>
      if containsSub line pat then
        some s!"{label}:{i + 1}: {pat}"
      else none

def main : IO UInt32 := do
  let root ← IO.currentDir
  unless (← (root / "lakefile.toml").pathExists) do
    throw <| IO.userError
      "check: lakefile.toml not found — run from the repository root"
  unless (← (root / "PLAN.md").pathExists) do
    throw <| IO.userError "check: PLAN.md not found in the repository root"
  let plan ← IO.FS.readFile (root / "PLAN.md")
  let parts := plan.splitOn partIIMarker
  if parts.length != 2 then
    IO.eprintln s!"check: expected exactly one '{partIIMarker}' marker in PLAN.md, found {parts.length - 1}"
    return 1
  let partI := parts[0]!
  let readme ← IO.FS.readFile (root / "README.md")
  let sources ← (root / "Meno").walkDir
  let mut hits : List String := sweep "PLAN.md(Part I)" partI
  hits := hits ++ sweep "README.md" readme
  for p in sources.qsort (fun a b => a.toString < b.toString) do
    if p.extension == some "lean" then
      let txt ← IO.FS.readFile p
      hits := hits ++ sweep (p.toString.drop (root.toString.length + 1)) txt
  let rootMeno ← IO.FS.readFile (root / "Meno.lean")
  hits := hits ++ sweep "Meno.lean" rootMeno
  if hits.isEmpty then
    IO.println "check: PASS (no retired identifiers in Part I, README, or sources)"
    return 0
  else
    IO.eprintln "check: FAIL — retired identifiers found:"
    for h in hits do
      IO.eprintln s!"  {h}"
    return 1
