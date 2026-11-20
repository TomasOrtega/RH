import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCondQdPde
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EX.szRow_cond_qd_pde` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSzRowCondQdPde.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  first | exact @GlobalTheory.EX.szRow_cond_qd_pde | exact GlobalTheory.EX.szRow_cond_qd_pde | (intros; apply GlobalTheory.EX.szRow_cond_qd_pde <;> assumption)
