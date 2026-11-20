import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.re_diag_le_of_eigen_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBlockUnitaryDiagonalLeOfEigenvalueBound.lean&line=101#L101)
-/
theorem _root_.GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  first | exact @GlobalTheory.HoweR.re_diag_le_of_eigen_bound | exact GlobalTheory.HoweR.re_diag_le_of_eigen_bound | (intros; apply GlobalTheory.HoweR.re_diag_le_of_eigen_bound <;> assumption)
