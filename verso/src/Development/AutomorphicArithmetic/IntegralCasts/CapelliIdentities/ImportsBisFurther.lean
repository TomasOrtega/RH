import Mathlib

/- English proof (translation)
Introduce `o ι S _ _ _ _ f d hf c v`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : ∑ i, m i = d`. Establish `h` using `hf (MvPolynomial.mem_support_iff.mp hm)`.

Establish `h' : m.degree = d`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `h`. Rewrite using `[← h', Finsupp.degree_eq_sum]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.DYla1.main.{u_3, u_4, u_5} :
    ∀ {o : Type u_3} {ι : Type u_4} {S : Type u_5} [Fintype ι] [inst : CommRing o] [inst_1 : CommRing S]
      [inst_2 : Algebra o S] {f : MvPolynomial ι o} {d : ℕ},
      f.IsHomogeneous d →
        ∀ (c : S) (v : ι → S),
          (MvPolynomial.aeval fun (i : ι) ↦ c * v i : MvPolynomial ι o → S) f =
            c ^ d * (MvPolynomial.aeval v : MvPolynomial ι o → S) f := by
  intro o ι S _ _ _ _ f d hf c v
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h := hf (MvPolynomial.mem_support_iff.mp hm)
    have h' : m.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h', Finsupp.degree_eq_sum]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
