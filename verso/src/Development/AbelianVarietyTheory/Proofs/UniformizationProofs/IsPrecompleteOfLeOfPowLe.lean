import Mathlib

namespace GlobalTheory.PrecompleteOfPowLe

universe u

/- English proof (translation)
Establish `h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m` using `fun m =>`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨L, hL⟩` from `hJ.prec (f := fun n => f ((e + 1) * n)) (fun {m n} hmn => (hf (Nat.mul_le_mul_left (e + 1) hmn)).mono (Submodule.smul_mono_left (h1 m)))`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations.

Establish `hn : n ≤ (e + 1) * n` using `Nat.le_mul_of_pos_left n (Nat.succ_pos e)`. Conclude with `(hf hn).trans ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)))`.
-/
theorem isPrecomplete_of_le_of_pow_le {A : Type u} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [hJ : IsPrecomplete J A] : IsPrecomplete I A := by
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m =>
    calc I ^ ((e + 1) * m) ≤ I ^ (e * m) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right m (Nat.le_succ e))
      _ = (I ^ e) ^ m := pow_mul I e m
      _ ≤ J ^ m := Ideal.pow_right_mono he m
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := hJ.prec (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left (e + 1) hmn)).mono (Submodule.smul_mono_left (h1 m)))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ (e + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos e)
  exact (hf hn).trans ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)))

end GlobalTheory.PrecompleteOfPowLe
