import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ φ p h hp hφ σ`. Establish `key : ∀ k : ℕ, h ((φ ^ k) σ) = (p : ℤ) ^ k * h σ`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hφ, ih]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < orderOf φ` using `orderOf_pos φ`. Establish `hk` using `key (orderOf φ)`. Rewrite `hk` using `[pow_orderOf_eq_one, Equiv.Perm.one_apply]`.

Establish `hp1 : (1 : ℤ) < p` using `by exact_mod_cast (show 1 < p by omega)`. Establish `hp' : (1 : ℤ) < (p : ℤ) ^ (orderOf φ)` using `one_lt_pow₀ hp1 hpos.ne'`. Establish `hz : ((p : ℤ) ^ (orderOf φ) - 1) * h σ = 0` using `by linear_combination -hk`. Break down `mul_eq_zero.mp hz with h1 | h1` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h1`.
-/
theorem eq_zero_of_scaled_along_perm : ∀ (ι : Type) [Fintype ι] (φ : Equiv.Perm ι) (p : ℕ) (h : ι → ℤ), 2 ≤ p → (∀ σ, h (φ σ) = p * h σ) → ∀ σ, h σ = 0 := by
  intro ι _ φ p h hp hφ σ
  have key : ∀ k : ℕ, h ((φ ^ k) σ) = (p : ℤ) ^ k * h σ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hφ, ih]; ring
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hk := key (orderOf φ)
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at hk
  have hp1 : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp' : (1 : ℤ) < (p : ℤ) ^ (orderOf φ) := one_lt_pow₀ hp1 hpos.ne'
  have hz : ((p : ℤ) ^ (orderOf φ) - 1) * h σ = 0 := by linear_combination -hk
  rcases mul_eq_zero.mp hz with h1 | h1
  · linarith
  · exact h1

end GlobalTheory
