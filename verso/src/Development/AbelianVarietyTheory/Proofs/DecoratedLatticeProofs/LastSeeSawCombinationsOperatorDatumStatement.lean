import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.lastSeeSaw_combinations_operatorDatum : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)
