import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEq

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq`. Consider the case `exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq`. Consider the case `(apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)`.
-/
theorem iInf_sup_pow_eq_of_compatible :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first
  | exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | (apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)

end GlobalTheory
