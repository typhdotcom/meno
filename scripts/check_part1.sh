#!/usr/bin/env bash
# Enforced C12 acceptance check (PLAN Phase 43): Part I of PLAN.md must
# contain no retired identifier and no deleted path. Exits nonzero on any hit.
set -u
P2=$(rg -n '^# Part II' PLAN.md | head -1 | cut -d: -f1)
RETIRED='CycleBasis\b|CyclePresentation|IntegralCyclePresentation|PeriodLattice\.lean|FundamentalPresentation|fundamentalPresentation|r_eq_b1|exists_rebase_related|\brebase\b|toGramData|killed_releases_mass|TransitionComplexity|HomKernelCat|staleness banner|Q_symm :|gram_symm :|summable :.*field|of_posDef|finPrefixSum|wedgePotential|thetaCycleBasis|thetaIntegralPresentation|cycleIntegralPresentation|wedgeGraphIntegralPresentation|gramOf_fund|fundCyclesZ_mem'
HITS=$(awk -v p2="$P2" 'NR<p2' PLAN.md | rg -n "$RETIRED")
if [ -n "$HITS" ]; then
  echo "RETIRED IDENTIFIERS IN PART I:"; echo "$HITS"; exit 1
fi
echo "check_part1: PASS (no retired identifiers before Part II)"
