import Mathlib

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ n N c hN`. Establish `hc : N.charpoly = X ^ n`. Use `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Conclude with `sub_eq_zero.mp this.eq_zero`.

Establish `h1` using `Matrix.charpoly_sub_scalar (N + Matrix.scalar (Fin n) c) c`. Rewrite `h1` using `[add_sub_cancel_right, hc]`. Establish `hXC : ((X : k[X]) + C c).comp (X - C c) = X` using `by simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[comp_assoc, hXC, comp_X]`.

Use `_ = (X - C c) ^ n := by rw [← h1]; simp`.
-/
theorem charpoly_nilpotent_add_scalar : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  intro k _ n N c hN
  have hc : N.charpoly = X ^ n := by
    have := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.mp this.eq_zero
  have h1 := Matrix.charpoly_sub_scalar (N + Matrix.scalar (Fin n) c) c
  rw [add_sub_cancel_right, hc] at h1
  have hXC : ((X : k[X]) + C c).comp (X - C c) = X := by simp
  calc (N + Matrix.scalar (Fin n) c).charpoly
      = ((N + Matrix.scalar (Fin n) c).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [comp_assoc, hXC, comp_X]
    _ = (X - C c) ^ n := by rw [← h1]; simp

end GlobalTheory
