import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigConstantTermCone
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.ctBigCone` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBigConstantTermCone.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.big_constant_term_cone : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTBigCone := by
  first | exact @GlobalTheory.ThK.ctBigCone | exact GlobalTheory.ThK.ctBigCone | (intros; apply GlobalTheory.ThK.ctBigCone <;> assumption)
