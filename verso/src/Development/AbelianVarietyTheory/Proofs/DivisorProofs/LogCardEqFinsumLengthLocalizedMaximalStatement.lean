import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximal
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogCardEqFinsumLengthLocalizedMaximal.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.log_card_eq_finsum_length_localized_maximal : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N] [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B, ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  first | exact @GlobalTheory.CardLength.log_card_eq_finsum_length | exact GlobalTheory.CardLength.log_card_eq_finsum_length | (intros; apply GlobalTheory.CardLength.log_card_eq_finsum_length <;> assumption)
