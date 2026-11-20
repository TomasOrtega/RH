import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FlatModel.packSt | exact GlobalTheory.FlatModel.packSt | (intros; apply GlobalTheory.FlatModel.packSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.packing_statement_holds : PackSt := by
  first | exact @GlobalTheory.FlatModel.packSt | exact GlobalTheory.FlatModel.packSt | (intros; apply GlobalTheory.FlatModel.packSt <;> assumption)
