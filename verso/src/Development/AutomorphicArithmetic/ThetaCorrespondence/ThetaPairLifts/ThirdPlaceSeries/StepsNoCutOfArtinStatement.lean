import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StepsOfArtinReciprocityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCutOfArtin

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Pass.stepsNoCut_of_artin_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FStepsNoCutOfArtin.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.no_cut_passes_of_artin_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := by
  first | exact @_root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt | exact _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt | (intros; apply _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt <;> assumption)
end
