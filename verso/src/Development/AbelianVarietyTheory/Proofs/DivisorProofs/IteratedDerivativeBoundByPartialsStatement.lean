import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeBoundByPartials
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIteratedDerivativeBoundByPartials.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.iterated_derivative_bound_by_partials : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : X → ℂ), ContDiff ℝ ∞ g → ∀ (n : ℕ) (z : X),
      ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ C * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (Module.finBasis ℝ X i)) z‖ := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial | exact GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial | (intros; apply GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial <;> assumption)
