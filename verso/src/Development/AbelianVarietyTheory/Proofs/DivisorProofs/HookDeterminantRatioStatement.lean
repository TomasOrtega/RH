import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookDeterminantRatio
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHookDeterminantRatio.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.hook_determinant_ratio : ∀ (N k r : ℕ), r < k → k ≤ N → ∃ S : MvPolynomial (Fin N) ℝ, S.IsHomogeneous k ∧ (∀ m, 0 ≤ S.coeff m) ∧ eval (fun _ => 1) S = ((N + k - r - 1).choose k * (k - 1).choose r : ℕ) ∧ Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ hookRho N k r c) = S * Matrix.det (Matrix.of fun i c : Fin N => (X i : MvPolynomial (Fin N) ℝ) ^ rho N c) := by
  first | exact @GlobalTheory.HookSchur.exists_hookSchur | exact GlobalTheory.HookSchur.exists_hookSchur | (intros; apply GlobalTheory.HookSchur.exists_hookSchur <;> assumption)
