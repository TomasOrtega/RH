import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRow
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.tieRat_of` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalityOfTwistRow.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.rationality_of_twist_row : TwAdm → RowAt → TieRat := by
  first | exact @GlobalTheory.BigOn.Exp.tieRat_of | exact GlobalTheory.BigOn.Exp.tieRat_of | (intros; apply GlobalTheory.BigOn.Exp.tieRat_of <;> assumption)
