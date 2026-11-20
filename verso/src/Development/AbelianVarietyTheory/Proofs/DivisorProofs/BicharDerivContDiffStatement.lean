import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiff
import Mathlib
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBicharDerivContDiff.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) → (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) → ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  first | exact @GlobalTheory.bichar_deriv_contDiff | exact GlobalTheory.bichar_deriv_contDiff | (intros; apply GlobalTheory.bichar_deriv_contDiff <;> assumption)
