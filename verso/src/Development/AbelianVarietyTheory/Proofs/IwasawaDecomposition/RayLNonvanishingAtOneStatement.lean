import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLNonvanishingAtOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRayLNonvanishingAtOne.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.ray_L_nonvanishing_at_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  first | exact @GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | exact GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | (intros; apply GlobalTheory.Mem.rayLSeries_entire_ne_zero_one <;> assumption)
