import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataTailBoundClosedFormLargeGaps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalDataTailBoundClosedFormLargeGaps.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.localDataTailBound_closedForm_largeGaps : GlobalTheory.GapIn.Hyp → TailP := by
  first | exact @GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap | exact GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap | (intros; apply GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap <;> assumption)
