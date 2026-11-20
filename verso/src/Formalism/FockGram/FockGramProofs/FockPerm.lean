import Formalism.FockGram.StatementFock

open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E
namespace FockPermanent

variable {R τ : Type*} [CommRing R]

def bil (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.A.mfact m : R)

/- English proof (translation)
The claim follows from `Finset.sum_subset h (fun m _ hm => by have : f.coeff m = 0 := by simpa using hm simp [this])`.
-/
lemma bil_eq_of_subset {f g : MvPolynomial τ R} {S : Finset (τ →₀ ℕ)} (h : f.support ⊆ S) :
    bil f g = ∑ m ∈ S, f.coeff m * g.coeff m * (Formalism.A.mfact m : R) :=
  Finset.sum_subset h (fun m _ hm => by
    have : f.coeff m = 0 := by simpa using hm
    simp [this])

/- English proof (translation)
Rewrite using `[bil_eq_of_subset (S := f.support ∪ f'.support) support_add, bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_left, bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_right, ← sum_add_distrib]`. Use `sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma bil_add_left (f f' g : MvPolynomial τ R) : bil (f + f') g = bil f g + bil f' g := by
  classical
  rw [bil_eq_of_subset (S := f.support ∪ f'.support) support_add,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_left,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_right, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Rewrite using `[bil, bil, bil, ← sum_add_distrib]`. Use `sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma bil_add_right (f g g' : MvPolynomial τ R) : bil f (g + g') = bil f g + bil f g' := by
  rw [bil, bil, bil, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Establish `hc : Multiset.card (Finsupp.toMultiset d) = 1`. Rewrite using `[Finsupp.card_toMultiset, Finsupp.sum]`. Conclude with `h`. Take `⟨k, hk⟩` from `Multiset.card_eq_one.mp hc`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
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
Use extensionality with `n`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_C_mul, coeff_X]`. Distinguish the cases in `h0 : x.coeff n = 0`. Rewrite using `[h0]`.

Use `symm`. Apply `sum_eq_zero` to reduce the goal to its premises. Introduce `k _`. Use `split_ifs with h`. Rewrite using `[h, h0, mul_one]`.

Rewrite using `[mul_zero]`. Establish `hd : n.degree = 1`. Assume the negation of the conclusion as `hd`. Conclude with `h0 (hx.coeff_eq_zero hd)`. Take `⟨k, rfl⟩` from `deg1 n hd`.

Rewrite using `[sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`.

Conclude with `hb (Finsupp.single_left_injective one_ne_zero h)`. Introduce `hk`. It suffices to derive a contradiction. Apply `hk` to reduce the goal to its premises. Rewrite using `[mem_vars]`.

Conclude with `⟨Finsupp.single k 1, mem_support_iff.mpr h0, by simp⟩`.
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
Use extensionality with `m`. Rewrite using `[coeff_pderiv, coeff_C]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (Ne.symm hm), hz.coeff_eq_zero, zero_mul]`. Rewrite using `[map_add, Finsupp.degree_single]`. Introduce `h`. Apply `hm` to reduce the goal to its premises. Rewrite using `[← Finsupp.degree_eq_zero_iff]`.

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
