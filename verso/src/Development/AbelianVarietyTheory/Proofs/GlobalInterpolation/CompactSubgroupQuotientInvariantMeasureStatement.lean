import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSubgroupQuotientInvariantMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.QuotientMeasureCompact.compactClause | exact GlobalTheory.QuotientMeasureCompact.compactClause | (intros; apply GlobalTheory.QuotientMeasureCompact.compactClause <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  first | exact @GlobalTheory.QuotientMeasureCompact.compactClause | exact GlobalTheory.QuotientMeasureCompact.compactClause | (intros; apply GlobalTheory.QuotientMeasureCompact.compactClause <;> assumption)
