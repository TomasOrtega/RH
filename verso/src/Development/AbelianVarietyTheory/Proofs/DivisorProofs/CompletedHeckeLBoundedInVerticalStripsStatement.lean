import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompletedHeckeLBoundedInVerticalStrips.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  first | exact @GlobalTheory.HeckeStrip.completedLBoundedInStrips | exact GlobalTheory.HeckeStrip.completedLBoundedInStrips | (intros; apply GlobalTheory.HeckeStrip.completedLBoundedInStrips <;> assumption)
