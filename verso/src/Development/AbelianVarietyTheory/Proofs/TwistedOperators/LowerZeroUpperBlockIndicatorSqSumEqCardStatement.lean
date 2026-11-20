import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLowerZeroUpperBlockIndicatorSqSumEqCard.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
  ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  first | exact @GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | exact GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | (intros; apply GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card <;> assumption)
