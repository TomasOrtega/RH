import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTameInertiaElementActsByScalar.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.tameInertiaElement_acts_by_scalar : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  first | exact @GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | exact GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia | (intros; apply GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia <;> assumption)
