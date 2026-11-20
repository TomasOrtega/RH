import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `E _ _ a`. Take `⟨τ, -, hτ⟩` from `locSec E a (hOne E a) hOne_mem_cone`. Take `⟨ε, hε, hball⟩` from `Metric.nhds_basis_closedBall.eventually_iff.1 hτ`. Establish `hK : Metric.closedBall (hOne E a) ε ⊆ cone E a` using `fun p hp => ⟨τ p, hball hp⟩`. Take `⟨C, hC⟩` from `boundInf E a _ hK (isCompact_closedBall _ _)`.

Use `⟨ε, C, hε, fun Y hY => ?_⟩` and prove the remaining obligations. Establish `h1 : hOne E a ∈ Metric.closedBall (hOne E a) ε` using `Metric.mem_closedBall_self hε.le`. Establish `hp : hOne E a + hv Y ∈ Metric.closedBall (hOne E a) ε`. Rewrite using `[mem_closedBall_iff_norm, add_sub_cancel_left]`. Conclude with `hY`.

Establish `hs` using `hball hp`. Use `⟨τ (hOne E a + hv Y), ?_, hC _ _ h1 (by rw [hs]; exact hp), hC _ _ hp ?_⟩` and prove the remaining obligations. Establish `h2` using `sand_val (τ (hOne E a + hv Y)) (hOne E a)`. Rewrite `h2` using `[hs, hOne_val, mul_one]`. Conclude with `h2.symm`.

Establish `h3 : sand (τ (hOne E a + hv Y))⁻¹ (sand (τ (hOne E a + hv Y)) (hOne E a)) = hOne E a`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression. Rewrite `h3` using `[hs]`. Rewrite using `[h3]`.

Conclude with `h1`.
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
