import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermsVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConstantTermsVanish.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.constant_terms_vanish : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTBigZero ∧ GlobalTheory.ThK.CTSmallZero := by
  first | exact @GlobalTheory.ThKCtZero.ctZero | exact GlobalTheory.ThKCtZero.ctZero | (intros; apply GlobalTheory.ThKCtZero.ctZero <;> assumption)
