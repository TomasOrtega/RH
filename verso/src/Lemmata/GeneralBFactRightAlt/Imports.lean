import Mathlib

open MvPolynomial Matrix

namespace Bl.general_b_fact_right_alt

/- English proof (translation)
Use `conv_lhs => rw [G.as_sum]`. Use `conv_rhs => rw [G.as_sum]`. Simplify using `only [map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Simplify using `only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`.

Rewrite using `[← hG.degree_eq_sum_deg_support hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem goal1 {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {ι : Type*} [Fintype ι]
    {G : MvPolynomial ι K} {d : ℕ} (hG : IsHomogeneous G d) (c : S) (f : ι → S) :
    aeval (fun v => c * f v) G = c ^ d * aeval f G := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← hG.degree_eq_sum_deg_support hs]
  ring

end Bl.general_b_fact_right_alt
