import Meno.ThetaHarmonic
import Meno.ThetaBinding
import Meno.CycleHarmonic
import Meno.Groupoid

/-! # The completion certificate (review #18)

**Completion as a Lean object, not a prose ledger.** `MenoCompletion`
bundles the three generic law certificates — thermal duality
(`QuadLatticeAction.ThermalDualityLaws`), information
(`FinDist.InformationLaws`), and the resolution tower
(`IncidenceGraph.ResolutionTowerLaws`) — together with the flagship
concrete consumers: the cycle graph's T-duality through the spine,
the wedge's matter sector, and the theta graph's Siegel–Poisson
duality, binding, priced gravity/time faces, tower prices, and
thermal circle, closing with the geodesic–harmonic duality.

`menoCompletion` is its **one derivation**. Every field is a `Prop`
proved from the existing engines; an unfinished or incoherent field
would fail to compile. Acceptance inspects this statement and its
derivation routes — the certificate is what "the program is closed"
*means* in Lean.
-/

namespace Meno

universe u v

/- `thetaGraph` is reducible, so its projections reduce to concrete
types in instance goals and the generic instances' graph
metavariable cannot be solved by unification — apply them by name
(review #14 pattern, `Meno/ThetaHarmonic.lean`). -/

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionFintype 2

local instance : Nonempty (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionNonempty 2

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 4) :=
  thetaGraph.h1ReductionFintype 4

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 8) :=
  thetaGraph.h1ReductionFintype 8

noncomputable local instance :
    DecidableEq (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionDecEq 2

noncomputable local instance :
    DecidableEq (IncidenceGraph.H1Reduction thetaGraph 4) :=
  thetaGraph.h1ReductionDecEq 4

noncomputable local instance :
    Fintype (SGD.Pullback (thetaGraph.carrierCompression 2)
      (thetaGraph.carrierCompression 2)) :=
  thetaGraph.carrierPullbackFintype 2

local instance :
    Nonempty (SGD.Pullback (thetaGraph.carrierCompression 2)
      (thetaGraph.carrierCompression 2)) :=
  thetaGraph.carrierPullbackNonempty 2

/-- **THE COMPLETION CERTIFICATE** (review #18): the generic law
certificates and the flagship consumers, as one derived `Prop`.

* `thermal` — the thermal-duality laws of **every** bundled lattice
  action (duality, temperature, response: the C9/C12 analytic spine);
* `information` — the information laws of **every** finite
  distribution (the C9 information algebra);
* `tower` — the resolution-tower laws of **every** graph (the C9
  resolution calculus);
* `cycle_T_duality` — the cycle graph's T-duality through the spine
  (C1–C5's keystone consumers, C8);
* `wedge_matter` — the wedge carries matter (C6);
* `theta_binding` — attaching the face kills theta's matter (C7);
* `theta_duality` — the theta graph's non-diagonal Siegel–Poisson
  duality (C8);
* `gravity_time_faces` — gravity, time, all three bridge packages,
  and all three strict variances, priced on theta (C9);
* `theta_tower_prices` — the complete priced composition law on the
  theta tower `8 → 4 → 2` (C9);
* `theta_mean_equation`, `theta_variance_equation` — the
  temperature–duality circle on theta's non-diagonal carrier;
* `geodesic_duality` — the geodesic–harmonic duality on the cycle
  (C10). -/
structure MenoCompletion : Prop where
  thermal : ∀ Q : QuadLatticeAction.{u},
    QuadLatticeAction.ThermalDualityLaws Q
  information : ∀ {X : Type u} [Fintype X] [DecidableEq X]
    (P : FinDist X), FinDist.InformationLaws P
  tower : ∀ G : IncidenceGraph.{u, v},
    IncidenceGraph.ResolutionTowerLaws G
  cycle_T_duality : ∀ (n : ℕ) (hn : n ≥ 3),
    (↑(QuadraticAction.scalarPartFn (Real.pi ^ 2 * n)) : ℂ)
      = ↑((1 / (n : ℝ)) / Real.pi) ^ ((1 : ℂ) / 2)
        * ↑(Simplicial.partitionFn n hn)
  wedge_matter : ∀ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3),
    Nonempty (MatterSector (wedgeGraph n₁ n₂ (by omega) (by omega)))
  theta_binding :
    ¬ ∃ κ' : thetaFilled.h1, thetaFilled.restrict κ' = thetaMatter.val
  theta_duality :
    (↑(thetaHarmonicGramData.toQuadraticAction.dual.toSectorAction.partFn)
        : ℂ)
      = ↑((1/12 : ℝ) / Real.pi ^ 2) ^ ((1 : ℂ) / 2)
        * ↑(thetaHarmonicGramData.toQuadraticAction.toSectorAction.partFn)
  gravity_time_faces :
    ((thetaGraph.pairAction 2).partFn * (thetaGraph.residueAction 2).partFn
        = (thetaGraph.descriptionAction 2).partFn
          * (thetaGraph.descriptionAction 2).partFn)
      ∧ ((thetaGraph.pairAction 2).complexity
            + (thetaGraph.residueAction 2).complexity
          = (thetaGraph.descriptionAction 2).complexity
            + (thetaGraph.descriptionAction 2).complexity)
      ∧ (sectionCost (thetaGraph.carrierCompression 2)
            / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
          = (thetaGraph.descriptionAction 2).complexity
            - (thetaGraph.residueAction 2).complexity)
      ∧ ((uniformAction
              (IncidenceGraph.H1Reduction thetaGraph 2)).complexity
            = (thetaGraph.residueAction 2).complexity
              + (thetaGraph.residueAction 2).gibbsExpect
                  (thetaGraph.residueAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.residueAction 2).complexity
          ∧ 0 < (thetaGraph.residueAction 2).gibbsExpect
              (thetaGraph.residueAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ ((uniformAction (thetaGraph.E → ZMod 2)).complexity
            = (thetaGraph.descriptionAction 2).complexity
              + (thetaGraph.descriptionAction 2).gibbsExpect
                  (thetaGraph.descriptionAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.descriptionAction 2).complexity
          ∧ 0 < (thetaGraph.descriptionAction 2).gibbsExpect
              (thetaGraph.descriptionAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ ((uniformAction (SGD.Pullback (thetaGraph.carrierCompression 2)
              (thetaGraph.carrierCompression 2))).complexity
            = (thetaGraph.pairAction 2).complexity
              + (thetaGraph.pairAction 2).gibbsExpect
                  (thetaGraph.pairAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.pairAction 2).complexity
          ∧ 0 < (thetaGraph.pairAction 2).gibbsExpect
              (thetaGraph.pairAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ 0 < (thetaGraph.residueAction 2).gibbsVariance
          (thetaGraph.residueAction 2).E
      ∧ 0 < (thetaGraph.descriptionAction 2).gibbsVariance
          (thetaGraph.descriptionAction 2).E
      ∧ 0 < (thetaGraph.pairAction 2).gibbsVariance
          (thetaGraph.pairAction 2).E
  theta_tower_prices :
    ((thetaGraph.residueDist 8).condEntropy
          (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
        = (thetaGraph.residueDist 8).condEntropy
              (⇑(thetaGraph.h1TowerMap 4 8 (by norm_num)))
          + (thetaGraph.residueDist 4).condEntropy
              (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num))))
      ∧ sectionCost (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
            / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
          = sectionCost (⇑(thetaGraph.h1TowerMap 4 8 (by norm_num)))
                / Nat.card (IncidenceGraph.H1Reduction thetaGraph 4)
            + sectionCost (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
                / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
      ∧ (thetaGraph.residueDist 8).condEntropy
            (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
          = 2 * Real.log 4
            - (thetaGraph.residueDefect 8 - thetaGraph.residueDefect 2)
  theta_mean_equation : ∀ (β : ℝ), 0 < β →
    thetaGraph.classMeanEnergy β
        + β⁻¹ ^ 2 * (thetaGraph.cycleAction).meanEnergy β⁻¹
      = 1 / β
  theta_variance_equation : ∀ (β : ℝ) (hβ : 0 < β),
    (thetaGraph.classSectorActionβ β hβ).gibbsVariance
        thetaGraph.harmonicEnergy
      + 2 * β⁻¹ ^ 3 * (thetaGraph.cycleAction).meanEnergy β⁻¹
      - β⁻¹ ^ 4 * (((thetaGraph.cycleAction).scaledSector β⁻¹
          (inv_pos.mpr hβ)).gibbsVariance
          (fun c => (thetaGraph.cycleAction).form c c))
      = 1 / β ^ 2
  geodesic_duality : ∀ (n : ℕ) (hn : n ≥ 3),
    Geodesic.length (Simplicial.canonicalLoop n hn)
      * (cyclePeriodData n (by omega)).energy ![1] = 1

/-- **THE PROGRAM IS CLOSED** (review #18): the completion
certificate, derived. Every field routes through the named engines —
no field re-proves anything. -/
theorem menoCompletion : MenoCompletion.{u, v} where
  thermal := QuadLatticeAction.thermalDualityLaws
  information := fun P => FinDist.informationLaws P
  tower := IncidenceGraph.resolutionTowerLaws
  cycle_T_duality := partitionFn_T_duality_via_spine
  wedge_matter := wedge_exists_matter
  theta_binding := theta_binding_kills
  theta_duality := theta_siegelPoisson_duality
  gravity_time_faces := theta_priced_faces
  theta_tower_prices := theta_tower_price_triangle
  theta_mean_equation := fun β hβ => theta_classMeanEnergy_T_dual β hβ
  theta_variance_equation := fun β hβ => theta_gibbsVariance_T_dual β hβ
  geodesic_duality := Simplicial.geodesic_harmonic_duality

end Meno
