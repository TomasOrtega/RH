import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCentralElementsFromIdempotentCoeffs.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.central_elements_from_idempotent_coeffs : StepCentral := by
  first | exact @GlobalTheory.Pass.CentralStep.main | exact GlobalTheory.Pass.CentralStep.main | (intros; apply GlobalTheory.Pass.CentralStep.main <;> assumption)
