import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPow

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow`. Consider the case `exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow`. Consider the case `(apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow ..)`.
-/
theorem ringHom_apply_eq_pow_of_pow_pow_eq_self :
    ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N →
      ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  first
  | exact @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow
  | (apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedOfPower.ringHom_apply_eq_pow ..)

end GlobalTheory
