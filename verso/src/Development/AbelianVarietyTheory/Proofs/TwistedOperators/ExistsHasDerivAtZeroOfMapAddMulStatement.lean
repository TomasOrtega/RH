import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHasDerivAtZeroOfMapAddMul

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsHasDerivAtZeroOfMapAddMul.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' : ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 → ∃ a : ℂ, HasDerivAt ν a 0 := by
  first | exact @GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul | exact GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul | (intros; apply GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul <;> assumption)
