import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelRowsEqDimension

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FBaseLevelRowsEqDimension.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.ind_piece_degree_zero : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  first | exact @_root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt | exact _root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.base_level_rows_eq_dimension_alt <;> assumption)
end
