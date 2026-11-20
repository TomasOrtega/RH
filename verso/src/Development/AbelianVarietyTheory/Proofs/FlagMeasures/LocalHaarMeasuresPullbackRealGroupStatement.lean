import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PullbackComparison.pullC_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalHaarMeasuresPullbackRealGroup.lean&line=333#L333)
-/
theorem _root_.GlobalTheory.T.localHaarMeasures_pullback_realGroup : GlobalTheory.TypeAsm.PullC := by
  first | exact @GlobalTheory.PullbackComparison.pullC_holds | exact GlobalTheory.PullbackComparison.pullC_holds | (intros; apply GlobalTheory.PullbackComparison.pullC_holds <;> assumption)
