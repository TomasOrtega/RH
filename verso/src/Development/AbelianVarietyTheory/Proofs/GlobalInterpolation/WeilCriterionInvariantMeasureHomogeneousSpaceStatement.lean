import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FWeilCriterionInvariantMeasureHomogeneousSpace.lean&line=210#L210)
-/
theorem _root_.GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space : ModulusClause := by
  first | exact @GlobalTheory.WeilCriterion.modulusClause | exact GlobalTheory.WeilCriterion.modulusClause | (intros; apply GlobalTheory.WeilCriterion.modulusClause <;> assumption)
