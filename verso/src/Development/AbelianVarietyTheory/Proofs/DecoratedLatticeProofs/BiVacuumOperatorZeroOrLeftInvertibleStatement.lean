import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertible
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FBiVacuumOperatorZeroOrLeftInvertible.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.biVacuumOperator_zero_or_left_invertible : ∀ D : D7, GlobalTheory.FinPl.BiInv D := by
  first | exact @GlobalTheory.FinPl.biInv_main | exact GlobalTheory.FinPl.biInv_main | (intros; apply GlobalTheory.FinPl.biInv_main <;> assumption)
