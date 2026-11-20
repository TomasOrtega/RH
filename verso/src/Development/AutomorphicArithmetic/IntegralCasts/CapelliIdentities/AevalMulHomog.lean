import Mathlib

/- English proof (translation)
Introduce `n A G S _ _ _ P hP b x`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd ↦ ?_` and prove the remaining obligations. Establish `hdeg : ∑ i ∈ d.support, d i = n`. Establish `h` using `hP (MvPolynomial.mem_support_iff.mp hd)`.

Simplify `h` using `[Finsupp.weight_apply, Finsupp.sum]`. Simplify using `only [mul_pow]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Qk4.aeval_mul_homog :
    ∀ {n : ℕ} {A G S : Type} [inst : CommRing A]
    [inst_1 : CommRing S] [inst_2 : Algebra A S] {P : MvPolynomial G A},
    P.IsHomogeneous n →
      ∀ (b : S) (x : G → S),
        (MvPolynomial.aeval fun (g : G) ↦ b * x g : MvPolynomial G A → S) P =
          b ^ n * (MvPolynomial.aeval x : MvPolynomial G A → S) P := by
  intro n A G S _ _ _ P hP b x
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
