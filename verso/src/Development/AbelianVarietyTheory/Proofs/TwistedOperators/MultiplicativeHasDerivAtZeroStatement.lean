import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicativeHasDerivAtZero

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMultiplicativeHasDerivAtZero.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add : ∀ (lam : ℝ → ℂ), lam 0 = 1 → (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  first | exact @GlobalTheory.multiplicative_hasDerivAt_zero | exact GlobalTheory.multiplicative_hasDerivAt_zero | (intros; apply GlobalTheory.multiplicative_hasDerivAt_zero <;> assumption)
