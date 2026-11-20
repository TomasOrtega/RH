import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarGroupQuotientIntegralFormula
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsUniqueHaarGroupQuotientIntegralFormula.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula : NormaliseGroupClause := by
  first | exact @GlobalTheory.normaliseGroupClause_holds | exact GlobalTheory.normaliseGroupClause_holds | (intros; apply GlobalTheory.normaliseGroupClause_holds <;> assumption)
