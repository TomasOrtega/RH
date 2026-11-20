import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingOfComparison
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLiftingOfComparison.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.lifting_of_comparison : CmpSt → LiftSt := by
  first | exact @GlobalTheory.FlatModel.liftSt_of_cmpSt | exact GlobalTheory.FlatModel.liftSt_of_cmpSt | (intros; apply GlobalTheory.FlatModel.liftSt_of_cmpSt <;> assumption)
