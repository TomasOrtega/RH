import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTypeParameterSquarefree.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.type_parameter_squarefree : StepType := by
  first | exact @GlobalTheory.Pass.stepType_proof | exact GlobalTheory.Pass.stepType_proof | (intros; apply GlobalTheory.Pass.stepType_proof <;> assumption)
