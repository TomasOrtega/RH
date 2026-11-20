import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAllPartsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemZAndCuspOfSteps

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FMemZAndCuspOfSteps.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.prvG6_of_admissible_of_g6_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @_root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics | exact _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics | (intros; apply _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics <;> assumption)
end
