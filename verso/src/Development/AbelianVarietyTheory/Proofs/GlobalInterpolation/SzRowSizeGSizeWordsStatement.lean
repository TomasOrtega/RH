import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWords
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EX.szRow_sizeG_sizeWords` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSzRowSizeGSizeWords.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.sizes_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) := by
  first | exact @GlobalTheory.EX.szRow_sizeG_sizeWords | exact GlobalTheory.EX.szRow_sizeG_sizeWords | (intros; apply GlobalTheory.EX.szRow_sizeG_sizeWords <;> assumption)
