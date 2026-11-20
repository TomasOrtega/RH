import Mathlib

/- English proof (translation)
Introduce `τ φ n hφ c w`. Rewrite using `[MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : ∑ i ∈ d.support, d i = n`. Establish `h` using `hφ (MvPolynomial.mem_support_iff.mp hd)`.

Rewrite using `[← h, Finsupp.weight_apply, Finsupp.sum]`. Simplify using the standard rewrite rules. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous.{u_1} :
    ∀ {τ : Type u_1} {φ : MvPolynomial τ ℂ} {n : ℕ},
      φ.IsHomogeneous n →
        ∀ (c : ℂ) (w : τ → ℂ),
          (MvPolynomial.eval (c • w) : MvPolynomial τ ℂ → ℂ) φ = c ^ n * (MvPolynomial.eval w : MvPolynomial τ ℂ → ℂ) φ := by
  intro τ φ n hφ c w
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
