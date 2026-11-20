import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsRowOperatorStableDualWeylAndGLSubmodules
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Alc.good_nablaSq_and_submodules` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FIsRowOperatorStableDualWeylAndGLSubmodules.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.isRowOperatorStable_dualWeyl_and_GLSubmodules : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N), Good (nablaSq k N lam) ∧ ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), GlobalTheory.Published.IsGLSubmodule k N lam M → Good M := by
  first | exact @GlobalTheory.Alc.good_nablaSq_and_submodules | exact GlobalTheory.Alc.good_nablaSq_and_submodules | (intros; apply GlobalTheory.Alc.good_nablaSq_and_submodules <;> assumption)
