import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Pass.stepType_proof | exact GlobalTheory.Pass.stepType_proof | (intros; apply GlobalTheory.Pass.stepType_proof <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.type_parameter_squarefree : StepType := by
  first | exact @GlobalTheory.Pass.stepType_proof | exact GlobalTheory.Pass.stepType_proof | (intros; apply GlobalTheory.Pass.stepType_proof <;> assumption)
