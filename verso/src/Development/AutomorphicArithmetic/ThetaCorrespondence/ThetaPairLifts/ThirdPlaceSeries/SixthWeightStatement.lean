import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatementStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthWeightPurity

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSixthWeightPurity.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.purity_string_weight : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  first | exact @_root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt | exact _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt | (intros; apply _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt <;> assumption)
end
