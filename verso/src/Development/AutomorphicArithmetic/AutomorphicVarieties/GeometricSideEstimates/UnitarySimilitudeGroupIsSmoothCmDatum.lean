import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.unitarySimilitudeGroup_isSmooth_cmDatum :
    RootEx := by
  intro E _ _ a
  obtain ⟨τ, -, hτ⟩ := locSec E a (hOne E a) hOne_mem_cone
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hτ
  have hK : Metric.closedBall (hOne E a) ε ⊆ cone E a := fun p hp => ⟨τ p, hball hp⟩
  obtain ⟨C, hC⟩ := boundInf E a _ hK (isCompact_closedBall _ _)
  refine ⟨ε, C, hε, fun Y hY => ?_⟩
  have h1 : hOne E a ∈ Metric.closedBall (hOne E a) ε := Metric.mem_closedBall_self hε.le
  have hp : hOne E a + hv Y ∈ Metric.closedBall (hOne E a) ε := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left]
    exact hY
  have hs := hball hp
  refine ⟨τ (hOne E a + hv Y), ?_, hC _ _ h1 (by rw [hs]; exact hp), hC _ _ hp ?_⟩
  · have h2 := sand_val (τ (hOne E a + hv Y)) (hOne E a)
    rw [hs, hOne_val, mul_one] at h2
    exact h2.symm
  · have h3 : sand (τ (hOne E a + hv Y))⁻¹ (sand (τ (hOne E a + hv Y)) (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [hs] at h3
    rw [h3]; exact h1
