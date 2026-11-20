import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesPol

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FDesPol.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.polynomial_descent_estimate' : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.desPol_alt | exact _root_.GlobalTheory.BigTop.Fun.desPol_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.desPol_alt <;> assumption)
end
