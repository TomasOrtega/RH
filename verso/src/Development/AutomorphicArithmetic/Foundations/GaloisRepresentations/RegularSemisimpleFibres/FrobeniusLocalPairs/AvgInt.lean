import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization

noncomputable section

open MeasureTheory
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 U hUo F hF q`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc`. Use `set u : K → ℂ := fun y => F (q * (y : G)) with hu`. Use `set S : Subgroup K := GlobalTheory.BCT.rStab u with hS`. Establish `hUS : U.subgroupOf K ≤ S`.

Introduce `k hk`. Establish `hk' : (k : G) ∈ U` using `Subgroup.mem_subgroupOf.mp hk`. Use `show ∀ x : K, u (x * k) = u x`. Introduce `x`. Simplify using `only [hu, Subgroup.coe_mul, ← mul_assoc]`.

Conclude with `hF _ hk' _`. Establish `hSo : IsOpen (S : Set K)` using `Subgroup.isOpen_mono hUS (Subgroup.subgroupOf_isOpen K U hUo)`. Use `haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo`. Use `letI : Fintype (K ⧸ S) := Fintype.ofFinite _`. Establish `hconst : ∀ y : K, u y = u (Quotient.out (QuotientGroup.mk y : K ⧸ S))`.

Introduce `y`. Establish `hmem : (Quotient.out (QuotientGroup.mk y : K ⧸ S))⁻¹ * y ∈ S`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`. Establish `h` using `hmem (Quotient.out (QuotientGroup.mk y : K ⧸ S))`. Rewrite `h` using `[mul_inv_cancel_left]`.

Conclude with `h`. Use `set S' : Set G := ((↑) : K → G) '' (S : Set K) with hS'`. Establish `hS'o : IsOpen S'` using `hKo.isOpenMap_subtype_val _ hSo`. Use `set A : K ⧸ S → Set G := fun c => (fun y => ((Quotient.out c : K) : G)⁻¹ * y) ⁻¹' S' with hA`. Establish `hmemA : ∀ c y, y ∈ A c ↔ ∃ h : y ∈ K, (QuotientGroup.mk (⟨y, h⟩ : K) : K ⧸ S) = c`.

Introduce `c y`. Simplify using `only [hA, hS', Set.mem_preimage, Set.mem_image, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsy⟩`. Establish `hy : y = ((Quotient.out c : K) : G) * (s : G)`.

Rewrite using `[hsy]`. Use `group`. Establish `hyK : y ∈ K`. Rewrite using `[hy]`. Conclude with `K.mul_mem (Quotient.out c).2 s.2`.

Use `⟨hyK, ?_⟩` and prove the remaining obligations. Establish `he : (⟨y, hyK⟩ : K) = Quotient.out c * s` using `Subtype.ext hy`. Rewrite using `[he]`. Use `conv_rhs => rw [← QuotientGroup.out_eq' c]`. Rewrite using `[QuotientGroup.eq]`.

Simplify `hs` using `[mul_assoc]`. Introduce and unpack `⟨hyK, hc⟩`. Establish `hmem : (Quotient.out c)⁻¹ * (⟨y, hyK⟩ : K) ∈ S`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq', hc]`. Conclude with `⟨_, hmem, by simp⟩`.

Establish `hAm : ∀ c, MeasurableSet (A c)` using `fun c => (measurable_const_mul _) hS'o.measurableSet`. Establish `hAK : ∀ c, A c ⊆ K` using `fun c y hy => ((hmemA c y).mp hy).1`. Establish `hAμ : ∀ c, μ (A c) = μ S'` using `fun c => measure_preimage_mul μ _ S'`. Establish `hunion : (⋃ c, A c) = (K : Set G)`. Apply `Set.Subset.antisymm (Set.iUnion_subset hAK)` to reduce the goal to its premises.

Introduce `y hy`. Conclude with `Set.mem_iUnion.mpr ⟨_, (hmemA _ y).mpr ⟨hy, rfl⟩⟩`. Establish `hdisj : Pairwise (Function.onFun Disjoint A)`. Introduce `c c' hcc'`. Use `Set.disjoint_left.mpr fun y h1 h2 => hcc' ?_` and prove the remaining obligations.

Take `⟨h, rfl⟩` from `(hmemA c y).mp h1`. Take `⟨h', rfl⟩` from `(hmemA c' y).mp h2`. Both sides reduce to the same expression. Establish `hsum : (Fintype.card (K ⧸ S) : ℝ≥0∞) * μ S' = 1`. Rewrite using `[← hK1, ← hunion, measure_iUnion hdisj hAm, tsum_fintype]`.

Simplify using `only [hAμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hcard : (Fintype.card (K ⧸ S) : ℕ) = S.index`. Rewrite using `[Subgroup.index_eq_card, Nat.card_eq_fintype_card]`. Establish `hreal : ∀ c, μ.real (A c) = ((S.index : ℝ))⁻¹`. Introduce `c`.

Establish `hne : (Fintype.card (K ⧸ S) : ℝ≥0∞) ≠ 0`. Simplify using the standard rewrite rules. Establish `h1 : μ S' = ((Fintype.card (K ⧸ S) : ℝ≥0∞))⁻¹`. Rewrite `hsum` using `[← ENNReal.eq_div_iff hne (by simp), ENNReal.div_eq_inv_mul, mul_one]`. Conclude with `hsum`.

Rewrite using `[Measure.real, hAμ, h1, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard]`. Use `haveI : IsFiniteMeasure (μ.restrict (K : Set G)) := ⟨by rw [Measure.restrict_apply_univ, hK1]; exact ENNReal.one_lt_top⟩`. Establish `hint : ∫ y in (K : Set G), F (q * y) ∂μ = ∫ y in (K : Set G), ∑ c, (A c).indicator (fun _ => u (Quotient.out c)) y ∂μ`. Use `setIntegral_congr_fun hKo.measurableSet fun y hy => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : K) : K ⧸ S)]`.

Rewrite using `[Set.indicator_of_mem ((hmemA _ y).mpr ⟨hy, rfl⟩)]`. Conclude with `hconst ⟨y, hy⟩`. Introduce `c _ hc`. Use `Set.indicator_of_notMem (fun h => hc ?_) _` and prove the remaining obligations. Take `⟨h', rfl⟩` from `(hmemA c y).mp h`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hint, integral_finset_sum _ fun c _ => (integrable_const _).indicator (hAm c)]`. Unfold `GlobalTheory.BCT.avg`.

Rewrite using `[finsum_eq_sum_of_fintype, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator_const _ (hAm c), measureReal_restrict_apply (hAm c), Set.inter_eq_left.mpr (hAK c), hreal c, Complex.real_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem avgInt : AvgInt := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 U hUo F hF q
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set u : K → ℂ := fun y => F (q * (y : G)) with hu
  set S : Subgroup K := GlobalTheory.BCT.rStab u with hS
  have hUS : U.subgroupOf K ≤ S := by
    intro k hk
    have hk' : (k : G) ∈ U := Subgroup.mem_subgroupOf.mp hk
    show ∀ x : K, u (x * k) = u x
    intro x
    simp only [hu, Subgroup.coe_mul, ← mul_assoc]
    exact hF _ hk' _
  have hSo : IsOpen (S : Set K) := Subgroup.isOpen_mono hUS (Subgroup.subgroupOf_isOpen K U hUo)
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  letI : Fintype (K ⧸ S) := Fintype.ofFinite _
  have hconst : ∀ y : K, u y = u (Quotient.out (QuotientGroup.mk y : K ⧸ S)) := by
    intro y
    have hmem : (Quotient.out (QuotientGroup.mk y : K ⧸ S))⁻¹ * y ∈ S := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have h := hmem (Quotient.out (QuotientGroup.mk y : K ⧸ S))
    rw [mul_inv_cancel_left] at h
    exact h
  set S' : Set G := ((↑) : K → G) '' (S : Set K) with hS'
  have hS'o : IsOpen S' := hKo.isOpenMap_subtype_val _ hSo
  set A : K ⧸ S → Set G := fun c => (fun y => ((Quotient.out c : K) : G)⁻¹ * y) ⁻¹' S' with hA
  have hmemA : ∀ c y, y ∈ A c ↔ ∃ h : y ∈ K, (QuotientGroup.mk (⟨y, h⟩ : K) : K ⧸ S) = c := by
    intro c y
    simp only [hA, hS', Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨s, hs, hsy⟩
      have hy : y = ((Quotient.out c : K) : G) * (s : G) := by
        rw [hsy]
        group
      have hyK : y ∈ K := by
        rw [hy]
        exact K.mul_mem (Quotient.out c).2 s.2
      refine ⟨hyK, ?_⟩
      have he : (⟨y, hyK⟩ : K) = Quotient.out c * s := Subtype.ext hy
      rw [he]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hs
    · rintro ⟨hyK, hc⟩
      have hmem : (Quotient.out c)⁻¹ * (⟨y, hyK⟩ : K) ∈ S := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hc]
      exact ⟨_, hmem, by simp⟩
  have hAm : ∀ c, MeasurableSet (A c) := fun c => (measurable_const_mul _) hS'o.measurableSet
  have hAK : ∀ c, A c ⊆ K := fun c y hy => ((hmemA c y).mp hy).1
  have hAμ : ∀ c, μ (A c) = μ S' := fun c => measure_preimage_mul μ _ S'
  have hunion : (⋃ c, A c) = (K : Set G) := by
    apply Set.Subset.antisymm (Set.iUnion_subset hAK)
    intro y hy
    exact Set.mem_iUnion.mpr ⟨_, (hmemA _ y).mpr ⟨hy, rfl⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro c c' hcc'
    refine Set.disjoint_left.mpr fun y h1 h2 => hcc' ?_
    obtain ⟨h, rfl⟩ := (hmemA c y).mp h1
    obtain ⟨h', rfl⟩ := (hmemA c' y).mp h2
    rfl
  have hsum : (Fintype.card (K ⧸ S) : ℝ≥0∞) * μ S' = 1 := by
    rw [← hK1, ← hunion, measure_iUnion hdisj hAm, tsum_fintype]
    simp only [hAμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ S) : ℕ) = S.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hreal : ∀ c, μ.real (A c) = ((S.index : ℝ))⁻¹ := by
    intro c
    have hne : (Fintype.card (K ⧸ S) : ℝ≥0∞) ≠ 0 := by
      simp
    have h1 : μ S' = ((Fintype.card (K ⧸ S) : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.eq_div_iff hne (by simp), ENNReal.div_eq_inv_mul, mul_one] at hsum
      exact hsum
    rw [Measure.real, hAμ, h1, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard]
  haveI : IsFiniteMeasure (μ.restrict (K : Set G)) :=
    ⟨by rw [Measure.restrict_apply_univ, hK1]; exact ENNReal.one_lt_top⟩
  have hint : ∫ y in (K : Set G), F (q * y) ∂μ =
      ∫ y in (K : Set G), ∑ c, (A c).indicator (fun _ => u (Quotient.out c)) y ∂μ := by
    refine setIntegral_congr_fun hKo.measurableSet fun y hy => ?_
    rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : K) : K ⧸ S)]
    · rw [Set.indicator_of_mem ((hmemA _ y).mpr ⟨hy, rfl⟩)]
      exact hconst ⟨y, hy⟩
    · intro c _ hc
      refine Set.indicator_of_notMem (fun h => hc ?_) _
      obtain ⟨h', rfl⟩ := (hmemA c y).mp h
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hint, integral_finset_sum _ fun c _ => (integrable_const _).indicator (hAm c)]
  unfold GlobalTheory.BCT.avg
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_indicator_const _ (hAm c), measureReal_restrict_apply (hAm c),
    Set.inter_eq_left.mpr (hAK c), hreal c, Complex.real_smul]
  push_cast
  rfl

end UpperTheory.Gal.InertialTypesAlt.L
