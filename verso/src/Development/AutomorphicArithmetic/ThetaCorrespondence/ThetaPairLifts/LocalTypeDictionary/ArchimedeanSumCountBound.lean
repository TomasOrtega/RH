import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKCosetCountFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepthStatement

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumCount
/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem archimedean_sum_count_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := fun hP hD =>
  infCountK_of GlobalTheory.T.datumCountBound_largeData (_root_.GlobalTheory.T.theta_kCoset_count_formula hP) (GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound hD)
end GlobalTheory.SumCount
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.sum_count_bound_archimedean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := by
  first | exact @_root_.GlobalTheory.SumCount.archimedean_sum_count_bound | exact _root_.GlobalTheory.SumCount.archimedean_sum_count_bound | (intros; apply _root_.GlobalTheory.SumCount.archimedean_sum_count_bound <;> assumption)
end
