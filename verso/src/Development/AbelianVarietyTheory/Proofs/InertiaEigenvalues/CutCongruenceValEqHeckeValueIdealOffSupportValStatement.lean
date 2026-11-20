import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportVal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCutCongruenceValEqHeckeValueIdealOffSupportVal.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i), PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  first | exact @GlobalTheory.Pass.CutEq.main | exact GlobalTheory.Pass.CutEq.main | (intros; apply GlobalTheory.Pass.CutEq.main <;> assumption)
