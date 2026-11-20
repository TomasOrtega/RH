import Mathlib

open TensorProduct IsLocalRing Polynomial

namespace Bl.SecondBlockLemmaI

variable {A : Type} [CommRing A] (I : Ideal A)

/- English proof (translation)
Establish `hm : (X ^ 2 - X : A[X]).Monic`. Conclude with `monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))`. Establish `h0 : (X ^ 2 - X : A[X]).eval ε ∈ I`. Simplify using `only [eval_sub, eval_pow, eval_X]`. Rewrite using `[pow_two]`.

Conclude with `h`. Establish `hu : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : A[X]).derivative.eval ε))`. Establish `hd : (X ^ 2 - X : A[X]).derivative.eval ε = 2 * ε - 1`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_C]`. Evaluate the numerical expressions.

Rewrite using `[hd]`. Establish `hsq : (2 * ε - 1) * (2 * ε - 1) = 1 + 4 * (ε * ε - ε)` using `by ring`. Establish `hq : Ideal.Quotient.mk I ((2 * ε - 1) * (2 * ε - 1)) = 1`. Rewrite using `[hsq, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left 4 h), add_zero]`. Rewrite `hq` using `[map_mul]`.

Conclude with `⟨⟨_, _, hq, hq⟩, rfl⟩`. Take `⟨a, ha, hae⟩` from `HenselianRing.is_henselian (I := I) _ hm ε h0 hu`. Use `⟨a, ?_, hae⟩` and prove the remaining obligations. Use `ha.eq_zero` as an intermediate fact. Simplify using `only [eval_sub, eval_pow, eval_X] at this`.

Rewrite using `[← pow_two]`. Conclude with `sub_eq_zero.mp this`.
-/
theorem goal1 [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  have hm : (X ^ 2 - X : A[X]).Monic := by
    exact monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  have h0 : (X ^ 2 - X : A[X]).eval ε ∈ I := by
    simp only [eval_sub, eval_pow, eval_X]
    rw [pow_two]; exact h
  have hu : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : A[X]).derivative.eval ε)) := by
    have hd : (X ^ 2 - X : A[X]).derivative.eval ε = 2 * ε - 1 := by
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow,
        eval_X, eval_one, eval_C]
      norm_num
    rw [hd]
    have hsq : (2 * ε - 1) * (2 * ε - 1) = 1 + 4 * (ε * ε - ε) := by ring
    have hq : Ideal.Quotient.mk I ((2 * ε - 1) * (2 * ε - 1)) = 1 := by
      rw [hsq, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left 4 h), add_zero]
    rw [map_mul] at hq
    exact ⟨⟨_, _, hq, hq⟩, rfl⟩
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) _ hm ε h0 hu
  refine ⟨a, ?_, hae⟩
  have := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X] at this
  rw [← pow_two]; exact sub_eq_zero.mp this

end Bl.SecondBlockLemmaI
