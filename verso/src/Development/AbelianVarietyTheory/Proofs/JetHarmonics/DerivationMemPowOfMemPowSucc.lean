import Mathlib

namespace GlobalTheory.DerivationMemPow

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `x hx`.

Rewrite `hx` using `[pow_succ]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations.

Conclude with `Ideal.mul_mem_right _ _ ha`. Establish `h` using `Ideal.mul_mem_mul hb (ih a ha)`. Rewrite `h` using `[← pow_succ']`. Then use the resulting hypothesis. Introduce `y z hy hz`. Rewrite using `[map_add]`.

Conclude with `Ideal.add_mem _ hy hz`.
-/
theorem derivation_mem_pow_of_mem_pow_succ {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (I : Ideal A) (n : ℕ) :
    ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ ha
      · have h := Ideal.mul_mem_mul hb (ih a ha)
        rwa [← pow_succ'] at h
    · intro y z hy hz
      rw [map_add]
      exact Ideal.add_mem _ hy hz

/- English proof (translation)
Introduce `D I n` and use `derivation_mem_pow_of_mem_pow_succ D I n`.
-/
example : ∀ {k A : Type} [inst : CommRing k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (D : Derivation k A A) (I : Ideal A) (n : ℕ), ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n :=
  fun D I n => derivation_mem_pow_of_mem_pow_succ D I n

end GlobalTheory.DerivationMemPow
