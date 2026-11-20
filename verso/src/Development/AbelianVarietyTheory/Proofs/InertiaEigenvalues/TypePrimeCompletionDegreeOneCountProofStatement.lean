import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTypePrimeCompletionDegreeOneCountProof.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof : StepDeg := by
  first | exact @GlobalTheory.Pass.stepDeg_main | exact GlobalTheory.Pass.stepDeg_main | (intros; apply GlobalTheory.Pass.stepDeg_main <;> assumption)
