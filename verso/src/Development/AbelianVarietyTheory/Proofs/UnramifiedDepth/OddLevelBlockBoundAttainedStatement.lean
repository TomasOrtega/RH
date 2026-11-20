import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttained
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.oddBlock_supply` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FOddLevelBlockBoundAttained.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.oddLevelBlock_bound_attained : BiSupply ∧ RF.BiSupply := by
  first | exact @GlobalTheory.oddBlock_supply | exact GlobalTheory.oddBlock_supply | (intros; apply GlobalTheory.oddBlock_supply <;> assumption)
