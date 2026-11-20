import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Pass.stepSub_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTwistedGaloisRepCharacterBlocks.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.twisted_galois_rep_character_blocks : StepSub := by
  first | exact @GlobalTheory.Pass.stepSub_holds | exact GlobalTheory.Pass.stepSub_holds | (intros; apply GlobalTheory.Pass.stepSub_holds <;> assumption)
