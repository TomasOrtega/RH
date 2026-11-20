import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicNonnegIntegralPos
import Mathlib
open MeasureTheory Set
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.integral_unitCube_pos_of_periodic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodicNonnegIntegralPos.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.periodic_nonneg_integral_pos : ∀ (ι : Type) [Fintype ι] (f : (ι → ℝ) → ℝ), Continuous f → (∀ x, 0 ≤ f x) → (∀ (x : ι → ℝ) (n : ι → ℤ), f (x + fun i => (n i : ℝ)) = f x) → (∃ x, f x ≠ 0) → 0 < ∫ x in Icc (0 : ι → ℝ) 1, f x := by
  first | exact @GlobalTheory.integral_unitCube_pos_of_periodic | exact GlobalTheory.integral_unitCube_pos_of_periodic | (intros; apply GlobalTheory.integral_unitCube_pos_of_periodic <;> assumption)
