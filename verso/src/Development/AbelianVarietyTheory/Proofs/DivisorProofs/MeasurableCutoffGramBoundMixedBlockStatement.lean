import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)
