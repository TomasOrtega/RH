import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypings
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MonBlock.monSupply` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FMonomialBlockSupplyBothTypings.lean&line=197#L197)
-/
theorem _root_.GlobalTheory.T.monomialBlock_supply_both_typings : MONSupply ∧ RF.MONSupply := by
  first | exact @GlobalTheory.MonBlock.monSupply | exact GlobalTheory.MonBlock.monSupply | (intros; apply GlobalTheory.MonBlock.monSupply <;> assumption)
