import Mathlib

/- English proof (translation)
Introduce `R _ I D n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `r _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `r hr`. Rewrite `hr` using `[pow_succ]`. Use `Submodule.mul_induction_on hr ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_` and prove the remaining obligations. Rewrite using `[pow_succ, mul_comm b]`. Conclude with `Ideal.mul_mem_mul (ih ha) hb`. Introduce `x y hx hy`.

Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ hx hy`.
-/
theorem UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ :
    ∀ {R : Type} [inst : CommRing R]
    (I : Ideal R) (D : Derivation ℤ R R) {n : ℕ} {r : R}, r ∈ I ^ (n + (1 : ℕ)) → (D : R → R) r ∈ I ^ n := by
  intro R _ I D n
  induction n with
  | zero =>
    intro r _
    simp
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (ih ha) hb
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy
