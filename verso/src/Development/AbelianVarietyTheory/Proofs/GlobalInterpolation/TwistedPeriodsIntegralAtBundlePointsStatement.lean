import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodsIntegralAtBundlePoints
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTwistedPeriodsIntegralAtBundlePoints.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.twistedPeriods_integral_at_bundlePoints : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols | exact GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols | (intros; apply GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols <;> assumption)
