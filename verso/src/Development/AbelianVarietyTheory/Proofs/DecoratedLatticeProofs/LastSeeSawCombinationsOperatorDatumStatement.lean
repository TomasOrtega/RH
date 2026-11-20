import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLastSeeSawCombinationsOperatorDatum.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.lastSeeSaw_combinations_operatorDatum : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)
