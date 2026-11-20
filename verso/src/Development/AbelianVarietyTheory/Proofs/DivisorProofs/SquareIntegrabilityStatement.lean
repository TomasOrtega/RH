import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrability
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
/- English proof (citation)
Apply `GlobalTheory.ThK.sqInt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSquareIntegrability.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.square_integrability : GlobalTheory.ThK.KP → GlobalTheory.ThK.SqInt := by
  first | exact @GlobalTheory.ThK.sqInt | exact GlobalTheory.ThK.sqInt | (intros; apply GlobalTheory.ThK.sqInt <;> assumption)
