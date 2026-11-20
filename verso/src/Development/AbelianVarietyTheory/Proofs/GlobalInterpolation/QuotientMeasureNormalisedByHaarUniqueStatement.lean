import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureNormalisedByHaarUnique
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | exact GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | (intros; apply GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normalise …`.
-/
theorem _root_.GlobalTheory.T.quotientMeasure_normalised_by_haar_unique : NormaliseQuotientClause := by
  first | exact @GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | exact GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | (intros; apply GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause <;> assumption)
