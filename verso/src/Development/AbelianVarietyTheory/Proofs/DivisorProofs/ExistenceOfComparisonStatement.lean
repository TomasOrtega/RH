import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatModel.exSt_of_cmpSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistenceOfComparison.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.existence_of_comparison : CmpSt → ExSt := by
  first | exact @GlobalTheory.FlatModel.exSt_of_cmpSt | exact GlobalTheory.FlatModel.exSt_of_cmpSt | (intros; apply GlobalTheory.FlatModel.exSt_of_cmpSt <;> assumption)
