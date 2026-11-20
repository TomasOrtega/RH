import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrankStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Establish `h0 : v.1 x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Unfold `ord`. Rewrite using `[map_inv₀, WithZero.log_inv, neg_neg]`.
-/
theorem functionFieldPlaceOrder_inv {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (hx : x ≠ 0) :
    ord v x⁻¹ = - ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ord
  rw [map_inv₀, WithZero.log_inv, neg_neg]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `inv_mem (IntermediateField.mem_adjoin_simple_self k x)`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Use `inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem adjoin_simple_inv_eq (k F : Type) [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮x⁻¹⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

/- English proof (translation)
Introduce `k F _ _ _ _ _ hF x hx`. Distinguish the cases in `htr : Transcendental k x`. Establish `htr' : Transcendental k x⁻¹`. Introduce `h`. Apply `htr` to reduce the goal to its premises.

Use `h.inv` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Take `⟨hA, hsA⟩` from `GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x htr`. Take `⟨hB, hsB⟩` from `GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x⁻¹ htr'`. Rewrite `hsB` using `[adjoin_simple_inv_eq]`.

Use `set A := {v : Place k F | v.1 x < 1}`. Use `set B := {v : Place k F | v.1 x⁻¹ < 1}`. Establish `hsub : {v : Place k F | v.1 x ≠ 1} ⊆ A ∪ B`. Introduce `v hv`. Establish `h0 : v.1 x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`.

Break down `lt_or_gt_of_ne hv with h | h` into its components or cases. Conclude with `Or.inl h`. Use `right show v.1 x⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ h`.

Use `⟨(hA.union hB).subset hsub, ?_⟩` and prove the remaining obligations. Establish `hpt : ∀ v : Place k F, ord v x = A.indicator (fun w => ord w x) v - B.indicator (fun w => ord w x⁻¹) v`. Introduce `v`. Establish `h0 : v.1 x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Break down `lt_trichotomy (v.1 x) 1 with h | h | h` into its components or cases.

Establish `hB' : v ∉ B` using `by show ¬ v.1 x⁻¹ < 1`. Rewrite using `[map_inv₀, not_lt]`. Conclude with `(one_le_inv₀ (zero_lt_iff.2 h0)).2 h.le`. Rewrite using `[Set.indicator_of_mem (show v ∈ A from h), Set.indicator_of_notMem hB', sub_zero]`. Establish `e : ord v x = 0` using `by unfold ord; rw [h, WithZero.log_one, neg_zero]`.

Rewrite using `[e, Set.indicator_of_notMem (show v ∉ A from fun h' => by change v.1 x < 1 at h'; rw [h] at h'; exact lt_irrefl _ h'), Set.indicator_of_notMem (show v ∉ B from by show ¬ v.1 x⁻¹ < 1`. Rewrite using `[map_inv₀, h, inv_one]`. Conclude with `lt_irrefl _)]`. Simplify using the standard rewrite rules. Establish `hA' : v ∉ A` using `fun h' => lt_asymm h h'`.

Establish `hB' : v ∈ B` using `by show v.1 x⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ h`. Rewrite using `[Set.indicator_of_notMem hA', Set.indicator_of_mem hB', functionFieldPlaceOrder_inv v x hx, zero_sub, neg_neg]`. Establish `hfA : (Function.support (A.indicator fun w => ord w x)).Finite` using `hA.subset (Set.support_indicator_subset)`.

Establish `hfB : (Function.support (B.indicator fun w => ord w x⁻¹)).Finite` using `hB.subset (Set.support_indicator_subset)`. Rewrite using `[finsum_congr hpt, finsum_sub_distrib hfA hfB, ← finsum_mem_def, ← finsum_mem_def, hsA, hsB, sub_self]`. Establish `halg : IsAlgebraic k x`. Assume the negation of the conclusion as `h`. Conclude with `htr h`.

Establish `hint : IsIntegral k x` using `halg.isIntegral`. Establish `hdeg : (minpoly k x).degree = 1` using `IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)`. Take `⟨c, rfl⟩` from `minpoly.mem_range_of_degree_eq_one k x hdeg`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx (map_zero _)`. Establish `hv : ∀ v : Place k F, v.1 (algebraMap k F c) = 1` using `fun v => v.2.2 c hc`. Use `⟨by simp [hv], ?_⟩` and prove the remaining obligations. Establish `: ∀ v : Place k F, ord v (algebraMap k F c) = 0`. Introduce `v`.

Unfold `ord`. Rewrite using `[hv v, WithZero.log_one, neg_zero]`. Simplify using `[this]`.
-/
theorem finite_support_and_sum_ord_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  intro k F _ _ _ _ _ hF x hx
  by_cases htr : Transcendental k x
  · have htr' : Transcendental k x⁻¹ := by
      intro h
      apply htr
      have := h.inv
      rwa [inv_inv] at this
    obtain ⟨hA, hsA⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x htr
    obtain ⟨hB, hsB⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x⁻¹ htr'
    rw [adjoin_simple_inv_eq] at hsB
    set A := {v : Place k F | v.1 x < 1}
    set B := {v : Place k F | v.1 x⁻¹ < 1}
    have hsub : {v : Place k F | v.1 x ≠ 1} ⊆ A ∪ B := by
      intro v hv
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_or_gt_of_ne hv with h | h
      · exact Or.inl h
      · right
        show v.1 x⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ h
    refine ⟨(hA.union hB).subset hsub, ?_⟩
    have hpt : ∀ v : Place k F, ord v x = A.indicator (fun w => ord w x) v - B.indicator (fun w => ord w x⁻¹) v := by
      intro v
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_trichotomy (v.1 x) 1 with h | h | h
      · have hB' : v ∉ B := by
          show ¬ v.1 x⁻¹ < 1
          rw [map_inv₀, not_lt]
          exact (one_le_inv₀ (zero_lt_iff.2 h0)).2 h.le
        rw [Set.indicator_of_mem (show v ∈ A from h), Set.indicator_of_notMem hB', sub_zero]
      · have e : ord v x = 0 := by unfold ord; rw [h, WithZero.log_one, neg_zero]
        rw [e, Set.indicator_of_notMem (show v ∉ A from fun h' => by change v.1 x < 1 at h'; rw [h] at h'; exact lt_irrefl _ h'),
          Set.indicator_of_notMem (show v ∉ B from by
            show ¬ v.1 x⁻¹ < 1
            rw [map_inv₀, h, inv_one]; exact lt_irrefl _)]
        simp
      · have hA' : v ∉ A := fun h' => lt_asymm h h'
        have hB' : v ∈ B := by
          show v.1 x⁻¹ < 1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h
        rw [Set.indicator_of_notMem hA', Set.indicator_of_mem hB', functionFieldPlaceOrder_inv v x hx, zero_sub, neg_neg]
    have hfA : (Function.support (A.indicator fun w => ord w x)).Finite :=
      hA.subset (Set.support_indicator_subset)
    have hfB : (Function.support (B.indicator fun w => ord w x⁻¹)).Finite :=
      hB.subset (Set.support_indicator_subset)
    rw [finsum_congr hpt, finsum_sub_distrib hfA hfB, ← finsum_mem_def, ← finsum_mem_def, hsA, hsB, sub_self]
  · have halg : IsAlgebraic k x := by
      by_contra h
      exact htr h
    have hint : IsIntegral k x := halg.isIntegral
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one k x hdeg
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hv : ∀ v : Place k F, v.1 (algebraMap k F c) = 1 := fun v => v.2.2 c hc
    refine ⟨by simp [hv], ?_⟩
    have : ∀ v : Place k F, ord v (algebraMap k F c) = 0 := by
      intro v; unfold ord; rw [hv v, WithZero.log_one, neg_zero]
    simp [this]

end GlobalTheory.Nef
