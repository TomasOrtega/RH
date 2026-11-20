import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookTranslationInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHookTranslationInvariant.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.hook_translation_invariant : ∀ (N k : ℕ) (a : ℝ), 2 ≤ k → k ≤ N → aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (hookR N k) = hookR N k ∧ aeval (fun i : Fin N => (X i + C a : MvPolynomial (Fin N) ℝ)) (detE (rho N)) = detE (rho N) := by
  first | exact @GlobalTheory.FlagHookShift.shift_invariant | exact GlobalTheory.FlagHookShift.shift_invariant | (intros; apply GlobalTheory.FlagHookShift.shift_invariant <;> assumption)
