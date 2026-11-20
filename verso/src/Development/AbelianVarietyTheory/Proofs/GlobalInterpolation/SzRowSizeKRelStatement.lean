import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRel
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.EX.szRow_sizeKRel | exact GlobalTheory.EX.szRow_sizeKRel | (intros; apply GlobalTheory.EX.szRow_sizeKRel <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.sizes_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeKRel | exact GlobalTheory.EX.szRow_sizeKRel | (intros; apply GlobalTheory.EX.szRow_sizeKRel <;> assumption)
