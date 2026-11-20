import ReciprocityTheory.DualLattices.FischerAdjointStatement

noncomputable section

open MvPolynomial Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def fw (A : Fin ν × ι →₀ ℕ) : ℂ := ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

/- English proof (translation)
Establish `hv : v ∈ insert v B.support` using `Finset.mem_insert_self v B.support`. Establish `h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support`. Introduce `x hx`. Rewrite `hx` using `[Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]`. Rewrite using `[Finset.mem_insert, Finsupp.mem_support_iff]`.

Distinguish the cases in `hxv : x = v`. Conclude with `Or.inl hxv`. Use `right`. Rewrite `hx` using `[if_neg (Ne.symm hxv), add_zero]`. Then use the resulting hypothesis. Establish `h2 : B.support ⊆ insert v B.support` using `Finset.subset_insert v B.support`.

Establish `hrest : ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial = ∏ x ∈ (insert v B.support).erase v, (B x).factorial`. Use `Finset.prod_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = (∏ x ∈ insert v B.support, (B x).factorial) * (B v + 1) := by`. Rewrite using `[← Finset.mul_prod_erase _ _ hv]`. Use `_ = B.prod (fun _ e => e.factorial) * (B v + 1) := by`. Rewrite using `[Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => Nat.factorial_zero)]`.
-/
private theorem finsupp_prod_factorial_add_single_one (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = B.prod (fun _ e => e.factorial) * (B v + 1) := by
  have hv : v ∈ insert v B.support := Finset.mem_insert_self v B.support
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hx
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hxv : x = v
    · exact Or.inl hxv
    · right
      rwa [if_neg (Ne.symm hxv), add_zero] at hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert v B.support
  have hrest : ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial
      = ∏ x ∈ (insert v B.support).erase v, (B x).factorial := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hx).symm, add_zero]
  calc (B + Finsupp.single v 1).prod (fun _ e => e.factorial)
      = ∏ x ∈ insert v B.support, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => Nat.factorial_zero)
    _ = ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) v).factorial
          * ∏ x ∈ (insert v B.support).erase v, ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial :=
        (Finset.mul_prod_erase _ (fun x => ((B + Finsupp.single v 1 : Fin ν × ι →₀ ℕ) x).factorial) hv).symm
    _ = (B v).factorial * (∏ x ∈ (insert v B.support).erase v, (B x).factorial) * (B v + 1) := by
        rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]; ring
    _ = (∏ x ∈ insert v B.support, (B x).factorial) * (B v + 1) := by
        rw [← Finset.mul_prod_erase _ _ hv]
    _ = B.prod (fun _ e => e.factorial) * (B v + 1) := by
        rw [Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => Nat.factorial_zero)]

/- English proof (translation)
Unfold `fw`. Rewrite using `[finsupp_prod_factorial_add_single_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]`.
-/
theorem fw_add_single (B : Fin ν × ι →₀ ℕ) (v : Fin ν × ι) :
    fw (B + Finsupp.single v 1) = fw B * ((B v : ℂ) + 1) := by
  unfold fw
  rw [finsupp_prod_factorial_add_single_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/- English proof (translation)
Establish `key : ∀ T : Finset (Fin ν × ι →₀ ℕ), P.support ⊆ T → ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A`. Introduce `T hT`. Use `symm`. Apply `Finset.sum_subset hT` to reduce the goal to its premises. Introduce `A _ hA`.

Establish `h0 : coeff A P = 0` using `by simpa [MvPolynomial.mem_support_iff] using hA`. Simplify using `[h0]`. Combine the equalities or inequalities in the displayed calculation. Unfold `fischer`. Conclude with `key _ (fun x hx => Finset.mem_union_left _ hx)`.

Use `_ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm`.
-/
theorem fischer_eq_sum (P Q : MvPolynomial (Fin ν × ι) ℂ) (S : Finset (Fin ν × ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), P.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A P = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm

/- English proof (translation)
Establish `hsub : (P + P').support ⊆ P.support ∪ P'.support`. Introduce `A hA`. Rewrite `hA` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_add]`. Rewrite using `[Finset.mem_union, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_or, ne_eq, not_not] at h`. Rewrite `hA` using `[h.1, h.2, add_zero]`. Conclude with `hA rfl`. Rewrite using `[fischer_eq_sum (P + P') Q (P.support ∪ P'.support) hsub, fischer_eq_sum P Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx), fischer_eq_sum P' Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fischer_add_left (P P' Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (P + P') Q = fischer P Q + fischer P' Q := by
  have hsub : (P + P').support ⊆ P.support ∪ P'.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hA
    rw [Finset.mem_union, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    rw [h.1, h.2, add_zero] at hA
    exact hA rfl
  rw [fischer_eq_sum (P + P') Q (P.support ∪ P'.support) hsub,
    fischer_eq_sum P Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx),
    fischer_eq_sum P' Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Establish `hsub : (c • P).support ⊆ P.support`. Introduce `A hA`. Rewrite `hA` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul]`. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h`.

Apply `hA` to reduce the goal to its premises. Rewrite using `[h, smul_zero]`. Rewrite using `[fischer_eq_sum (c • P) Q P.support hsub, fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fischer_smul_left (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (c • P) Q = c * fischer P Q := by
  have hsub : (c • P).support ⊆ P.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul] at hA
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hA
    rw [h, smul_zero]
  rw [fischer_eq_sum (c • P) Q P.support hsub,
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[fischer_eq_sum P (Q + Q') P.support (Finset.Subset.refl _), fischer_eq_sum P Q P.support (Finset.Subset.refl _), fischer_eq_sum P Q' P.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fischer_add_right (P Q Q' : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (Q + Q') = fischer P Q + fischer P Q' := by
  rw [fischer_eq_sum P (Q + Q') P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q' P.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add, map_add]
  ring

/- English proof (translation)
Rewrite using `[fischer_eq_sum P (c • Q) P.support (Finset.Subset.refl _), fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fischer_smul_right (c : ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (c • Q) = starRingEnd ℂ c * fischer P Q := by
  rw [fischer_eq_sum P (c • Q) P.support (Finset.Subset.refl _),
    fischer_eq_sum P Q P.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul]
  ring

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_empty]`. Rewrite using `[fischer_eq_sum P 0 P.support (Finset.Subset.refl _)]`. Simplify using the standard rewrite rules. Introduce `a t ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]`.
-/
theorem fischer_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial (Fin ν × ι) ℂ)
    (f : α → MvPolynomial (Fin ν × ι) ℂ) :
    fischer P (∑ i ∈ s, f i) = ∑ i ∈ s, fischer P (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum P 0 P.support (Finset.Subset.refl _)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_empty]`. Rewrite using `[fischer_eq_sum 0 Q ∅ (by simp)]`. Simplify using the standard rewrite rules. Introduce `a t ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]`.
-/
theorem fischer_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin ν × ι) ℂ)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (∑ i ∈ s, f i) Q = ∑ i ∈ s, fischer (f i) Q := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    rw [fischer_eq_sum 0 Q ∅ (by simp)]
    simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

/- English proof (translation)
Establish `hsub : (C c : MvPolynomial (Fin ν × ι) ℂ).support ⊆ {0}`. Introduce `A hA`. Rewrite `hA` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C]`. Rewrite using `[Finset.mem_singleton]`. Assume the negation of the conclusion as `h`.

Conclude with `hA (if_neg (fun e => h e.symm))`. Rewrite using `[fischer_eq_sum (C c) Q {0} hsub, Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl]`. Simplify using `[fw]`.
-/
theorem fischer_C_left (c : ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (C c) Q = c * starRingEnd ℂ (coeff 0 Q) := by
  have hsub : (C c : MvPolynomial (Fin ν × ι) ℂ).support ⊆ {0} := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hA
    rw [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (fun e => h e.symm))
  rw [fischer_eq_sum (C c) Q {0} hsub, Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl]
  simp [fw]

/- English proof (translation)
Establish `key : ∀ T : Finset (Fin ν × ι →₀ ℕ), Q.support ⊆ T → ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A`. Introduce `T hT`. Use `symm`. Apply `Finset.sum_subset hT` to reduce the goal to its premises. Introduce `A _ hA`.

Establish `h0 : coeff A Q = 0` using `by simpa [MvPolynomial.mem_support_iff] using hA`. Simplify using `[h0]`. Combine the equalities or inequalities in the displayed calculation. Unfold `fischer`. Conclude with `key _ (fun x hx => Finset.mem_union_right _ hx)`.

Use `_ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm`.
-/
private theorem fischer_eq_sum_of_support_subset (P Q : MvPolynomial (Fin ν × ι) ℂ)
    (S : Finset (Fin ν × ι →₀ ℕ)) (hS : Q.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), Q.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A Q = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_right _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm

/- English proof (translation)
Rewrite using `[fischer_eq_sum_of_support_subset P (monomial m b) {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]`.
-/
private theorem fischer_monomial_right (P : MvPolynomial (Fin ν × ι) ℂ)
    (m : Fin ν × ι →₀ ℕ) (b : ℂ) :
    fischer P (monomial m b) = coeff m P * starRingEnd ℂ b * fw m := by
  rw [fischer_eq_sum_of_support_subset P (monomial m b) {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on'`. Use `next m b =>`. Rewrite using `[MvPolynomial.pderiv_monomial, fischer_monomial_right, fischer_monomial_right, MvPolynomial.coeff_mul_X']`. Use `split_ifs with h`. Establish `hv : m v ≠ 0` using `Finsupp.mem_support_iff.1 h`.

Establish `hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m`. Use extensionality with `x`. Rewrite using `[Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`. Use `split_ifs with hx`. Substitute `hx` using the available equality.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hw : fw m = fw (m - Finsupp.single v 1) * (m v : ℂ)`. Establish `h1` using `fw_add_single (m - Finsupp.single v 1) v`. Rewrite `h1` using `[hm, Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv), Nat.cast_one, sub_add_cancel]`.

Conclude with `h1`. Rewrite using `[hw, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : m v = 0` using `by simpa [Finsupp.mem_support_iff] using h`. Rewrite using `[hv]`.

Simplify using the standard rewrite rules. Use `next Q₁ Q₂ h₁ h₂ =>`. Rewrite using `[fischer_add_right, map_add, fischer_add_right, h₁, h₂]`.
-/
theorem fischer_mul_X (P Q : MvPolynomial (Fin ν × ι) ℂ) (v : Fin ν × ι) :
    fischer (P * X v) Q = fischer P (pderiv v Q) := by
  induction Q using MvPolynomial.induction_on'
  next m b =>
    rw [MvPolynomial.pderiv_monomial, fischer_monomial_right, fischer_monomial_right,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have hv : m v ≠ 0 := Finsupp.mem_support_iff.1 h
      have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := by
        ext x
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hx
        · subst hx
          omega
        · omega
      have hw : fw m = fw (m - Finsupp.single v 1) * (m v : ℂ) := by
        have h1 := fw_add_single (m - Finsupp.single v 1) v
        rw [hm, Finsupp.tsub_apply, Finsupp.single_eq_same,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv), Nat.cast_one, sub_add_cancel] at h1
        exact h1
      rw [hw, map_mul, map_natCast]
      ring
    · have hv : m v = 0 := by simpa [Finsupp.mem_support_iff] using h
      rw [hv]
      simp
  next Q₁ Q₂ h₁ h₂ =>
    rw [fischer_add_right, map_add, fischer_add_right, h₁, h₂]

end ReciprocityTheory.PGsh
