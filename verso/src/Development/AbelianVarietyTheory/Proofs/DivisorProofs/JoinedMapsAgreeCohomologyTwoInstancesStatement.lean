import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJoinedMapsAgreeCohomologyTwoInstances.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := by
  first | exact @GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst | exact GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst | (intros; apply GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst <;> assumption)
