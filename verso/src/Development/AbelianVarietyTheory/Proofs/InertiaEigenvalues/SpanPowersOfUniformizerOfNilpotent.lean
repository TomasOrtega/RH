import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `C B _ _ φ π L e m hsurj he hm`. Establish `step1 : ∀ k : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B, x = ∑ j ∈ Finset.range k, φ (c j) * π ^ j + π ^ k * w`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x; exact ⟨0, x, by simp⟩`.

Consider the case `succ k ih`. Introduce `x`. Take `⟨c, w, hx⟩` from `ih x`. Take `⟨y, hy⟩` from `hsurj w`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp hy`.

Use `⟨fun j => if j = k then y else c j, z, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ]`. Use `beta_reduce`. Rewrite using `[if_pos rfl]`. Establish `hsum : ∑ j ∈ Finset.range k, φ (if j = k then y else c j) * π ^ j = ∑ j ∈ Finset.range k, φ (c j) * π ^ j`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Rewrite using `[if_neg (Finset.mem_range.mp hj).ne]`. Rewrite using `[hsum, hx]`. Establish `hw : w = φ y + z * π` using `by rw [hz]; ring`.

Rewrite using `[hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `step1' : ∀ x : B, ∃ c : ℕ → C, ∃ w : B, x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L * w`. Introduce `x`. Take `⟨c, w, hx⟩` from `step1 e x`.

Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.mp he`. Conclude with `⟨c, u * w, by rw [hx, ← hu]; ring⟩`. Establish `step2 : ∀ n : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B, x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L ^ n * w`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro x; exact ⟨0, x, by simp⟩`. Consider the case `succ n ih`. Introduce `x`. Take `⟨c, w, hx⟩` from `ih x`. Take `⟨d, w', hw⟩` from `step1' w`.

Use `⟨fun j => c j + L ^ n * d j, w', ?_⟩` and prove the remaining obligations. Establish `key : ∑ j ∈ Finset.range e, φ (c j + L ^ n * d j) * π ^ j = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L ^ n * ∑ j ∈ Finset.range e, φ (d j) * π ^ j`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Simplify using `only [map_add, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hx, hw]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`.

Take `⟨c, w, hx⟩` from `step2 m x`. Use `⟨fun j => c j, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hm, zero_mul, add_zero]`. Conclude with `(Fin.sum_univ_eq_sum_range (fun j => φ (c j) * π ^ j) e).symm`.
-/
theorem span_powers_of_uniformizer_of_nilpotent :
    ∀ (C B : Type) [CommRing C] [CommRing B] (φ : C →+* B) (π : B) (L : C) (e m : ℕ),
      (∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π}) → π ^ e ∈ Ideal.span {φ L} → φ L ^ m = 0 →
      ∀ x : B, ∃ c : Fin e → C, x = ∑ j, φ (c j) * π ^ (j : ℕ) := by
  intro C B _ _ φ π L e m hsurj he hm
  have step1 : ∀ k : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range k, φ (c j) * π ^ j + π ^ k * w := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨c, w, hx⟩ := ih x
      obtain ⟨y, hy⟩ := hsurj w
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨fun j => if j = k then y else c j, z, ?_⟩
      rw [Finset.sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have hsum : ∑ j ∈ Finset.range k, φ (if j = k then y else c j) * π ^ j
          = ∑ j ∈ Finset.range k, φ (c j) * π ^ j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Finset.mem_range.mp hj).ne]
      rw [hsum, hx]
      have hw : w = φ y + z * π := by rw [hz]; ring
      rw [hw]; ring
  have step1' : ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L * w := by
    intro x
    obtain ⟨c, w, hx⟩ := step1 e x
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp he
    exact ⟨c, u * w, by rw [hx, ← hu]; ring⟩
  have step2 : ∀ n : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L ^ n * w := by
    intro n
    induction n with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨c, w, hx⟩ := ih x
      obtain ⟨d, w', hw⟩ := step1' w
      refine ⟨fun j => c j + L ^ n * d j, w', ?_⟩
      have key : ∑ j ∈ Finset.range e, φ (c j + L ^ n * d j) * π ^ j
          = ∑ j ∈ Finset.range e, φ (c j) * π ^ j
            + φ L ^ n * ∑ j ∈ Finset.range e, φ (d j) * π ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_add, map_mul, map_pow]
        ring
      rw [key, hx, hw]
      ring
  intro x
  obtain ⟨c, w, hx⟩ := step2 m x
  refine ⟨fun j => c j, ?_⟩
  rw [hx, hm, zero_mul, add_zero]
  exact (Fin.sum_univ_eq_sum_range (fun j => φ (c j) * π ^ j) e).symm

end GlobalTheory
