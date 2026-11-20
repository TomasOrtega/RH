import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
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
