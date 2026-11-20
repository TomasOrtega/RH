import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetAdResultant.det_ad_eq_resultant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDetCommutatorMapEqCharpolyResultant.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.det_commutator_map_eq_charpoly_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂), LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) = resultant f₁.charpoly f₂.charpoly := by
  first | exact @GlobalTheory.DetAdResultant.det_ad_eq_resultant | exact GlobalTheory.DetAdResultant.det_ad_eq_resultant | (intros; apply GlobalTheory.DetAdResultant.det_ad_eq_resultant <;> assumption)
