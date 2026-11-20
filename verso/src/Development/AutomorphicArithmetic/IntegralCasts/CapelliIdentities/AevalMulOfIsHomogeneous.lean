import Mathlib

/- English proof (translation)
Introduce `σ R _ _ _ P d hP y g`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `h1 : s.degree = d`. Assume the negation of the conclusion as `h`.

Conclude with `(MvPolynomial.mem_support_iff.1 hs) (hP.coeff_eq_zero h)`. Establish `h2 : ∑ i, s i = d`. Rewrite using `[← h1, Finsupp.degree_eq_sum]`. Repeatedly rewrite using `[mul_pow]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous :
    ∀ {σ R : Type} [Fintype σ]
    [inst : CommRing R] [inst_1 : Algebra ℚ R] {P : MvPolynomial σ ℚ} {d : ℕ},
    P.IsHomogeneous d →
      ∀ (y : R) (g : σ → R),
        (MvPolynomial.aeval fun (k : σ) ↦ y * g k : MvPolynomial σ ℚ → R) P =
          y ^ d * (MvPolynomial.aeval g : MvPolynomial σ ℚ → R) P := by
  intro σ R _ _ _ P d hP y g
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : s.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hs) (hP.coeff_eq_zero h)
  have h2 : ∑ i, s i = d := by
    rw [← h1, Finsupp.degree_eq_sum]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h2]
  ring
