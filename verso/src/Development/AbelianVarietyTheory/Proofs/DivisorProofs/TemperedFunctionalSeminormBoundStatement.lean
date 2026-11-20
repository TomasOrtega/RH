import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TemperedFunctionalSeminormBound
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTemperedFunctionalSeminormBound.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.tempered_functional_seminorm_bound : ∀ {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (T : SchwartzMap D ℂ →L[ℂ] ℂ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : SchwartzMap D ℂ,
      ‖T φ‖ ≤ C * ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ m n φ := by
  first | exact @GlobalTheory.schwartz_clm_bound_finite_seminorm_sum | exact GlobalTheory.schwartz_clm_bound_finite_seminorm_sum | (intros; apply GlobalTheory.schwartz_clm_bound_finite_seminorm_sum <;> assumption)
