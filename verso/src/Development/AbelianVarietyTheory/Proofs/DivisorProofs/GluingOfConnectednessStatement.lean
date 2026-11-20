import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluingOfConnectedness
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.glueSt_of` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGluingOfConnectedness.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.gluing_of_connectedness : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → GlueSt := by
  first | exact @GlobalTheory.FlatModel.glueSt_of | exact GlobalTheory.FlatModel.glueSt_of | (intros; apply GlobalTheory.FlatModel.glueSt_of <;> assumption)
