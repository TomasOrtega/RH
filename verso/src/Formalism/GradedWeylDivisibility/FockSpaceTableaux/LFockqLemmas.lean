import Formalism.GradedWeylDivisibility.StatementB

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

/- English proof (translation)
Unfold `fockQ`. Use `Finset.sum_subset h (fun m _ hm => ?_)` and prove the remaining obligations. Establish `hz : f.coeff m = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hm (MvPolynomial.mem_support_iff.mpr hne)`.

Simplify using `[hz]`.
-/
lemma lfockq_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset h (fun m _ hm => ?_)
  have hz : f.coeff m = 0 := by
    by_contra hne
    exact hm (MvPolynomial.mem_support_iff.mpr hne)
  simp [hz]

/- English proof (translation)
Rewrite using `[lfockq_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left, lfockq_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]`. Conclude with `Finset.sum_congr rfl (fun m _ => by ring)`.
-/
lemma lfockq_symm (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  classical
  rw [lfockq_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    lfockq_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/- English proof (translation)
Unfold `fockQ`. Establish `hne : f.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `he`. Conclude with `hf (MvPolynomial.support_eq_empty.mp he)`.

Use `Finset.sum_pos (fun m hm => ?_) hne` and prove the remaining obligations. Establish `hc : f.coeff m ≠ 0` using `MvPolynomial.mem_support_iff.mp hm`. Establish `hw : (0 : ℚ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ)` using `Nat.cast_pos.mpr (Finset.prod_pos (fun k _ => Nat.factorial_pos _))`. Conclude with `mul_pos (mul_self_pos.mpr hc) hw`.
-/
lemma lfockq_self_pos (f : MvPolynomial σ ℚ) (hf : f ≠ 0) : 0 < fockQ f f := by
  unfold fockQ
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hf (MvPolynomial.support_eq_empty.mp he)
  refine Finset.sum_pos (fun m hm => ?_) hne
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hw : (0 : ℚ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Finset.prod_pos (fun k _ => Nat.factorial_pos _))
  exact mul_pos (mul_self_pos.mpr hc) hw

/- English proof (translation)
Rewrite using `[lfockq_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add, lfockq_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left, lfockq_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)`.
-/
lemma lfockq_add_left (f f' g : MvPolynomial σ ℚ) :
    fockQ (f + f') g = fockQ f g + fockQ f' g := by
  classical
  rw [lfockq_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    lfockq_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    lfockq_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

/- English proof (translation)
Rewrite using `[lfockq_eq_sum (c • f) g f.support MvPolynomial.support_smul, lfockq_eq_sum f g f.support subset_rfl, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)`.
-/
lemma lfockq_smul_left (c : ℚ) (f g : MvPolynomial σ ℚ) :
    fockQ (c • f) g = c * fockQ f g := by
  rw [lfockq_eq_sum (c • f) g f.support MvPolynomial.support_smul,
    lfockq_eq_sum f g f.support subset_rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

end general

end Formalism.GradedWeylDivisibility
