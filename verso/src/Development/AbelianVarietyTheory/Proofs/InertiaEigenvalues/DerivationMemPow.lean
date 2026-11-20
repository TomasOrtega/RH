import Mathlib

namespace GlobalTheory.DerivationPowerIdeal

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite `hx` using `[pow_succ' I (n + 1)]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations.

Introduce `a ha b hb`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)` and prove the remaining obligations. Rewrite using `[pow_succ' I n]`. Conclude with `Ideal.mul_mem_mul ha (ih hb)`.

Introduce `a b ha hb`. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ ha hb`.
-/
theorem derivation_mem_pow {A' : Type} [CommRing A'] {k : Type} [CommRing k] [Algebra k A']
    (I : Ideal A') (D : Derivation k A' A') (n : ℕ) {x : A'} (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' I (n + 1)] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ' I n]
      exact Ideal.mul_mem_mul ha (ih hb)
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb

end GlobalTheory.DerivationPowerIdeal
