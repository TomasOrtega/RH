import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FCharacterBlocksAttainBound.lean&line=219#L219)
-/
theorem _root_.GlobalTheory.T.characterBlocks_attain_bound : CHSupply ∧ RF.CHSupply := by
  first | exact @GlobalTheory.CharBlock.chSupply | exact GlobalTheory.CharBlock.chSupply | (intros; apply GlobalTheory.CharBlock.chSupply <;> assumption)
