import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealSideColumnsCompatibleBundlePointsOverColumns
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fc.PeriodEntriesOverColumns.row_tie_of_overCols` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FRealSideColumnsCompatibleBundlePointsOverColumns.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.realSideColumnsCompatible_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.Row_tie Q Lk := by
  first | exact @GlobalTheory.Fc.PeriodEntriesOverColumns.row_tie_of_overCols | exact GlobalTheory.Fc.PeriodEntriesOverColumns.row_tie_of_overCols | (intros; apply GlobalTheory.Fc.PeriodEntriesOverColumns.row_tie_of_overCols <;> assumption)
