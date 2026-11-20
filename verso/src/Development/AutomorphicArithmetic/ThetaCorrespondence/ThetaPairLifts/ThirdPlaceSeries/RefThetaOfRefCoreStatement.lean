import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceThetaOfCoreStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefThetaOfRefCore

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RefSum.refTheta_of_refCore_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FRefThetaOfRefCore.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.refTheta_of_size_refCore : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.ReferenceCore → _root_.GlobalTheory.RefSum.ReferenceTheta := by
  first | exact @_root_.GlobalTheory.RefSum.refTheta_of_refCore_alt | exact _root_.GlobalTheory.RefSum.refTheta_of_refCore_alt | (intros; apply _root_.GlobalTheory.RefSum.refTheta_of_refCore_alt <;> assumption)
end
