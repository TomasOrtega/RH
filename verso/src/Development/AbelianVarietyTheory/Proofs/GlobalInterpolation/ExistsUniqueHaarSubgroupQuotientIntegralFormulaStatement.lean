import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarSubgroupQuotientIntegralFormula
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsUniqueHaarSubgroupQuotientIntegralFormula.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula : NormaliseSubgroupClause := by
  first | exact @GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause | exact GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause | (intros; apply GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause <;> assumption)
