import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FlatModel.tateSt | exact GlobalTheory.FlatModel.tateSt | (intros; apply GlobalTheory.FlatModel.tateSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.tate_statement_holds : TateSt := by
  first | exact @GlobalTheory.FlatModel.tateSt | exact GlobalTheory.FlatModel.tateSt | (intros; apply GlobalTheory.FlatModel.tateSt <;> assumption)
