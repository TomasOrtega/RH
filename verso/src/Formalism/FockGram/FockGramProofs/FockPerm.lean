import Formalism.FockGram.StatementFock

open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E
namespace FockPermanent

variable {R τ : Type*} [CommRing R]

def bil (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.A.mfact m : R)

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma bil_eq_of_subset {f g : MvPolynomial τ R} {S : Finset (τ →₀ ℕ)} (h : f.support ⊆ S) :
    bil f g = ∑ m ∈ S, f.coeff m * g.coeff m * (Formalism.A.mfact m : R) :=
  Finset.sum_subset h (fun m _ hm => by
    have : f.coeff m = 0 := by simpa using hm
    simp [this])

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
lemma bil_add_left (f f' g : MvPolynomial τ R) : bil (f + f') g = bil f g + bil f' g := by
  classical
  rw [bil_eq_of_subset (S := f.support ∪ f'.support) support_add,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_left,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_right, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
lemma bil_add_right (f g g' : MvPolynomial τ R) : bil f (g + g') = bil f g + bil f g' := by
  rw [bil, bil, bil, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
lemma deg1 (d : τ →₀ ℕ) (h : d.degree = 1) : ∃ k, d = Finsupp.single k 1 := by
  classical
  have hc : Multiset.card (Finsupp.toMultiset d) = 1 := by
    rw [Finsupp.card_toMultiset, Finsupp.sum]; exact h
  obtain ⟨k, hk⟩ := Multiset.card_eq_one.mp hc
  refine ⟨k, ?_⟩
  calc d = Multiset.toFinsupp (Finsupp.toMultiset d) := (Finsupp.toMultiset_toFinsupp d).symm
    _ = _ := by rw [hk]; simp

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. It suffices to derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
lemma lin_repr (x : MvPolynomial τ R) (hx : x.IsHomogeneous 1) :
    x = ∑ k ∈ x.vars, C (x.coeff (Finsupp.single k 1)) * X k := by
  classical
  ext n
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  by_cases h0 : x.coeff n = 0
  · rw [h0]; symm
    apply sum_eq_zero
    intro k _
    split_ifs with h
    · rw [h, h0, mul_one]
    · rw [mul_zero]
  · have hd : n.degree = 1 := by
      by_contra hd; exact h0 (hx.coeff_eq_zero hd)
    obtain ⟨k, rfl⟩ := deg1 n hd
    rw [sum_eq_single k]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; exact hb (Finsupp.single_left_injective one_ne_zero h)
    · intro hk; exfalso; apply hk
      rw [mem_vars]
      exact ⟨Finsupp.single k 1, mem_support_iff.mpr h0, by simp⟩

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
lemma pderiv_lin (z : MvPolynomial τ R) (hz : z.IsHomogeneous 1) (k : τ) :
    pderiv k z = C (z.coeff (Finsupp.single k 1)) := by
  classical
  ext m
  rw [coeff_pderiv, coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm), hz.coeff_eq_zero, zero_mul]
    rw [map_add, Finsupp.degree_single]
    intro h; apply hm
    rw [← Finsupp.degree_eq_zero_iff]; omega

end FockPermanent

end Formalism.E
