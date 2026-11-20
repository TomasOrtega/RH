import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Pass.JumpDualStep.jumpDual_main | exact GlobalTheory.Pass.JumpDualStep.jumpDual_main | (intros; apply GlobalTheory.Pass.JumpDualStep.jumpDual_main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof : StepJumpDual := by
  first | exact @GlobalTheory.Pass.JumpDualStep.jumpDual_main | exact GlobalTheory.Pass.JumpDualStep.jumpDual_main | (intros; apply GlobalTheory.Pass.JumpDualStep.jumpDual_main <;> assumption)
