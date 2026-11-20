import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerMapIsIntegralUnramifiedInvolutionEx
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIntegerMapIsIntegralUnramifiedInvolutionEx.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧ @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  first | exact @GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | exact GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr <;> assumption)
