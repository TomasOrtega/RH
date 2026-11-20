import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallConstantTermCone
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmallConstantTermCone.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.small_constant_term_cone : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTSmallCone := by
  first | exact @GlobalTheory.ConeSmall.ctSmallCone | exact GlobalTheory.ConeSmall.ctSmallCone | (intros; apply GlobalTheory.ConeSmall.ctSmallCone <;> assumption)
