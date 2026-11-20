import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FQuotientInvariantMeasureExistsUniqueUnimodular.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular : InvariantMeasureClause := by
  first | exact @GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause | exact GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause | (intros; apply GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause <;> assumption)
