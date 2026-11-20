import Mathlib

/- English proof (translation)
Introduce `σ _ h d hh t v`. Rewrite using `[MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : ∑ i, m i = d`. Establish `h1` using `hh (MvPolynomial.mem_support_iff.mp hm)`.

Rewrite using `[← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h1 := hh (MvPolynomial.mem_support_iff.mp hm)
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
