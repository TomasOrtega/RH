import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CharBlock.chSupply | exact GlobalTheory.CharBlock.chSupply | (intros; apply GlobalTheory.CharBlock.chSupply <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.characterBlocks_attain_bound : CHSupply ∧ RF.CHSupply := by
  first | exact @GlobalTheory.CharBlock.chSupply | exact GlobalTheory.CharBlock.chSupply | (intros; apply GlobalTheory.CharBlock.chSupply <;> assumption)
