import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeColumnValuationsBundlePointsOverColumn
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fc.Cv.row_level_valuations` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLevelPrimeColumnValuationsBundlePointsOverColumn.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.levelPrimeColumnValuations_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.Cv.row_level_valuations | exact GlobalTheory.Fc.Cv.row_level_valuations | (intros; apply GlobalTheory.Fc.Cv.row_level_valuations <;> assumption)
