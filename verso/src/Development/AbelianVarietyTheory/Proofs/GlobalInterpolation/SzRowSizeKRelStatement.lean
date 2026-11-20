import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRel
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EX.szRow_sizeKRel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSzRowSizeKRel.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.sizes_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeKRel | exact GlobalTheory.EX.szRow_sizeKRel | (intros; apply GlobalTheory.EX.szRow_sizeKRel <;> assumption)
