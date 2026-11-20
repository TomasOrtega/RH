import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace dividedDifferenceExpansion

/- English proof (translation)
Rewrite using `[← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j < l), ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l), Finset.filter_filter, Finset.filter_filter, mul_assoc]`. Use `congr 2`. Rewrite using `[Finset.prod_eq_single l]`. Introduce `b hb hbl`. Simplify using `only [Finset.mem_filter] at hb`.

Conclude with `absurd hb.2.2 hbl`. Introduce `h`. Conclude with `absurd (by simp) h`. Use `congr 1`. Use extensionality with `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)`. Introduce `h`.

Conclude with `⟨not_lt.mpr h.le, ne_of_gt h⟩`.
-/
theorem prod_split {M : Type*} [CommMonoid M] {r : ℕ} (l : Fin r) (f : Fin r → M) :
    ∏ j, f j = (∏ j ∈ Finset.univ.filter (fun j => j < l), f j) * f l *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), f j := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => j < l),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun j => ¬ j < l) (fun j => j = l),
    Finset.filter_filter, Finset.filter_filter, mul_assoc]
  congr 2
  · rw [Finset.prod_eq_single l]
    · intro b hb hbl
      simp only [Finset.mem_filter] at hb
      exact absurd hb.2.2 hbl
    · intro h
      exact absurd (by simp) h
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    · intro h
      exact ⟨not_lt.mpr h.le, ne_of_gt h⟩

noncomputable def stair {r : ℕ} (μ : Fin r →₀ ℕ) (k : ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  ∏ j : Fin r, X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) ^ μ j

/- English proof (translation)
Simplify using `[stair]`.
-/
theorem stair_zero {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ 0 = ∏ j, X (Sum.inl j) ^ μ j := by
  simp [stair]

/- English proof (translation)
Simplify using `[stair]`.
-/
theorem stair_top {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ r = ∏ j, X (Sum.inr j) ^ μ j := by
  simp [stair]

/- English proof (translation)
Establish `hg : (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) * (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) = X (Sum.inl l) ^ μ l - X (Sum.inr l) ^ μ l`. Rewrite using `[mul_comm]`. Conclude with `geom_sum₂_mul _ _ _`. Establish `hlo : ∀ k : ℕ, (l : ℕ) ≤ k → ∏ j ∈ Finset.univ.filter (fun j => j < l), (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j = ∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j`. Introduce `k hk`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : (j : ℕ) < l` using `Fin.lt_def.mp (Finset.mem_filter.mp hj).2`. Rewrite using `[if_pos (by omega)]`. Establish `hhi : ∀ k : ℕ, k ≤ (l : ℕ) + 1 → ∏ j ∈ Finset.univ.filter (fun j => l < j), (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j = ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j`. Introduce `k hk`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : (l : ℕ) < j` using `Fin.lt_def.mp (Finset.mem_filter.mp hj).2`. Rewrite using `[if_neg (by omega)]`. Unfold `stair`. Rewrite using `[prod_split l, prod_split l (fun j => (X (if (j : ℕ) < (l : ℕ) + 1 then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j), hlo l le_rfl, hlo (l + 1) (by omega), hhi l (by omega), hhi (l + 1) le_rfl, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]`.

Take the linear combination `((∏ j ∈ Finset.univ.filter (fun j => j < l), (X (Sum.inr j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j) * ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) * hg`.
-/
theorem term_eq {r : ℕ} (μ : Fin r →₀ ℕ) (l : Fin r) :
    (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      stair μ l - stair μ (l + 1) := by
  have hg : (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) =
      X (Sum.inl l) ^ μ l - X (Sum.inr l) ^ μ l := by
    rw [mul_comm]
    exact geom_sum₂_mul _ _ _
  have hlo : ∀ k : ℕ, (l : ℕ) ≤ k →
      ∏ j ∈ Finset.univ.filter (fun j => j < l),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (j : ℕ) < l := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_pos (by omega)]
  have hhi : ∀ k : ℕ, k ≤ (l : ℕ) + 1 →
      ∏ j ∈ Finset.univ.filter (fun j => l < j),
          (X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j =
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j := by
    intro k hk
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : (l : ℕ) < j := Fin.lt_def.mp (Finset.mem_filter.mp hj).2
    rw [if_neg (by omega)]
  unfold stair
  rw [prod_split l, prod_split l (fun j => (X (if (j : ℕ) < (l : ℕ) + 1 then Sum.inr j else Sum.inl j) :
      MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j), hlo l le_rfl, hlo (l + 1) (by omega),
    hhi l (by omega), hhi (l + 1) le_rfl, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
  linear_combination
    ((∏ j ∈ Finset.univ.filter (fun j => j < l), (X (Sum.inr j) : MvPolynomial (Fin r ⊕ Fin r) ℤ) ^ μ j) *
      ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) * hg

/- English proof (translation)
Repeatedly rewrite using `[term_eq]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => stair μ i - stair μ (i + 1)) r, Finset.sum_range_sub', stair_zero, stair_top]`.
-/
theorem sum_term_eq {r : ℕ} (μ : Fin r →₀ ℕ) :
    ∑ l : Fin r, (X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
      ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
        (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
        ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) =
      ∏ j, X (Sum.inl j) ^ μ j - ∏ j, X (Sum.inr j) ^ μ j := by
  simp_rw [term_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i => stair μ i - stair μ (i + 1)) r,
    Finset.sum_range_sub', stair_zero, stair_top]

/- English proof (translation)
Use `conv_lhs => rw [G.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_mul, rename_C, map_prod]`. Simplify using `[map_pow, rename_X]`.
-/
theorem rename_eq_sum {r : ℕ} (f : Fin r → Fin r ⊕ Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename f G = ∑ μ ∈ G.support, C (G.coeff μ) * ∏ j, X (f j) ^ μ j := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_mul, rename_C, map_prod]
  simp [map_pow, rename_X]

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff`. Simplify using `only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rename_divDiff {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ G.support, C (G.coeff μ) *
        ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
          (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
          ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
  simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/- English proof (translation)
Introduce `r m G hG`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_eq_sum, rename_eq_sum, ← Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[rename_divDiff, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun μ _ => by ring`. Introduce `l`. Break down `m with _ | d` into its components or cases. Establish `h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G = 0`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff`.

Use `Finset.sum_eq_zero fun μ hμ => ?_` and prove the remaining obligations. Establish `h` using `hG (mem_support_iff.mp hμ)`. Rewrite `h` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Establish `hl : μ l = 0`. Establish `h' : ∑ j, μ j = 0` using `by simpa using h`.

Conclude with `(Finset.sum_eq_zero_iff.mp h') l (Finset.mem_univ l)`. Simplify using `[hl]`. Rewrite using `[h0, map_zero]`. Conclude with `isHomogeneous_zero _ _ _`. Simplify using `using (BundleExamples.isHomogeneous_divDiff l hG).rename_isHomogeneous (f := finSumFinEquiv.symm)`.
-/
theorem proof : dividedDifferenceExpansion.Statement := by
  intro r m G hG
  refine ⟨?_, ?_⟩
  · rw [rename_eq_sum, rename_eq_sum, ← Finset.sum_sub_distrib]
    calc ∑ μ ∈ G.support, (C (G.coeff μ) * ∏ j, X (Sum.inl j) ^ μ j -
            C (G.coeff μ) * ∏ j, X (Sum.inr j) ^ μ j)
        = ∑ μ ∈ G.support, ∑ l : Fin r, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_congr rfl fun μ _ => by rw [← Finset.mul_sum, sum_term_eq, mul_sub]
      _ = ∑ l : Fin r, ∑ μ ∈ G.support, C (G.coeff μ) *
            ((X (Sum.inl l) - X (Sum.inr l) : MvPolynomial (Fin r ⊕ Fin r) ℤ) *
              ((∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
                (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
                ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j)) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun l _ => by
          rw [rename_divDiff, Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
  · intro l
    rcases m with _ | d
    · have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G = 0 := by
        unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff
        refine Finset.sum_eq_zero fun μ hμ => ?_
        have h := hG (mem_support_iff.mp hμ)
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
        have hl : μ l = 0 := by
          have h' : ∑ j, μ j = 0 := by simpa using h
          exact (Finset.sum_eq_zero_iff.mp h') l (Finset.mem_univ l)
        simp [hl]
      rw [h0, map_zero]
      exact isHomogeneous_zero _ _ _
    · simpa using (BundleExamples.isHomogeneous_divDiff l hG).rename_isHomogeneous
        (f := finSumFinEquiv.symm)

end dividedDifferenceExpansion

end GroundTheory.Heights₂.Heights.NumbersDVR
