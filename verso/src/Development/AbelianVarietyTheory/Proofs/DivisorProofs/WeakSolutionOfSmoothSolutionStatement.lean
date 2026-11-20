import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakSolutionOfSmoothSolution
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCA.weakSol_of_smooth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeakSolutionOfSmoothSolution.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.weakSolution_of_smooth_solution : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  first | exact @GlobalTheory.HCA.weakSol_of_smooth | exact GlobalTheory.HCA.weakSol_of_smooth | (intros; apply GlobalTheory.HCA.weakSol_of_smooth <;> assumption)
