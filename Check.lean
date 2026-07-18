/-! # The documentation acceptance check (PLAN, C12)

`lake exe check` — fail-closed by construction (any I/O error or
malformed structure exits nonzero): locates the repository root by
walking upward, requires exactly one Part II marker in `PLAN.md`,
and sweeps PLAN Part I, `README.md`, and every `.lean` file under
`Meno/` (plus `Meno.lean`) for retired identifiers and deleted
paths. In the Lean toolchain, not a shell script (review #8 and
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

def findRoot : IO System.FilePath := do
  let mut dir : System.FilePath ← IO.currentDir
  for _ in [0:8] do
    if (← (dir / "PLAN.md").pathExists) then
      return dir
    match dir.parent with
    | some p => dir := p
    | none => break
  throw <| IO.userError "check: PLAN.md not found walking up from cwd"

def sweep (label : String) (text : String) : List String :=
  (text.splitOn "\n").zipIdx.flatMap fun (line, i) =>
    blacklist.filterMap fun pat =>
      if containsSub line pat then
        some s!"{label}:{i + 1}: {pat}"
      else none

def main : IO UInt32 := do
  let root ← findRoot
  let plan ← IO.FS.readFile (root / "PLAN.md")
  let parts := plan.splitOn partIIMarker
  if parts.length != 2 then
    IO.eprintln s!"check: expected exactly one '{partIIMarker}' marker in PLAN.md, found {parts.length - 1}"
    return 1
  let partI := parts[0]!
  let readme ← IO.FS.readFile (root / "README.md")
  let menoDir := root / "Meno"
  let entries ← menoDir.readDir
  let mut hits : List String := sweep "PLAN.md(Part I)" partI
  hits := hits ++ sweep "README.md" readme
  for ent in entries do
    if ent.path.extension == some "lean" then
      let txt ← IO.FS.readFile ent.path
      hits := hits ++ sweep s!"Meno/{ent.fileName}" txt
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
