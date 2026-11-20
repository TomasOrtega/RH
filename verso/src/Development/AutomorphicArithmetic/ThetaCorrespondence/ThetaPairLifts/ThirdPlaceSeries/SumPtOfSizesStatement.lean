import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumericalStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizes

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RefSum.sumPt_of_sizes_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSumPtOfSizes.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.sum_pt_of_wt_pt_num_pt : _root_.GlobalTheory.RefSum.WtPtAlt → _root_.GlobalTheory.RefSum.NumPtAlt → _root_.GlobalTheory.RefSum.SumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.sumPt_of_sizes_alt | exact _root_.GlobalTheory.RefSum.sumPt_of_sizes_alt | (intros; apply _root_.GlobalTheory.RefSum.sumPt_of_sizes_alt <;> assumption)
end
