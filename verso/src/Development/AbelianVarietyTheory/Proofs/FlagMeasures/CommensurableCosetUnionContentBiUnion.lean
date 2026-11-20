import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonnegStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨W0, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩` and prove the remaining obligations. Consider the case `insert j s hj ih`. Take `⟨A, hA0, hA⟩` from `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`.

Take `⟨B, hB⟩` from `h j (Finset.mem_insert_self _ _)`. Establish `h1 : (A ⊓ B).relIndex A ≠ 0`. Rewrite using `[AddSubgroup.inf_relIndex_left]`. Conclude with `AddSubgroup.relIndex_ne_zero_trans hB.1 hA0.2.1`. Establish `h2 : (A ⊓ B).relIndex B ≠ 0`.

Rewrite using `[AddSubgroup.inf_relIndex_right]`. Conclude with `AddSubgroup.relIndex_ne_zero_trans hA0.1 hB.2.1`. Use `⟨A ⊓ B, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 ∅).2.1 A _ hA0 inf_le_left h1, fun i hi => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 B _ hB inf_le_right h2`.

Conclude with `(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 A _ (hA i hi) inf_le_left h1`.
-/
theorem exists_common_goodSub {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type}
    (s : Finset ι) (S : ι → Set W) (h : ∀ i ∈ s, IsCO W0 (S i)) :
    ∃ A, GoodSub W0 A ∅ ∧ ∀ i ∈ s, GoodSub W0 A (S i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨W0, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
  | insert j s hj ih =>
    obtain ⟨A, hA0, hA⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨B, hB⟩ := h j (Finset.mem_insert_self _ _)
    have h1 : (A ⊓ B).relIndex A ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_left]
      exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA0.2.1
    have h2 : (A ⊓ B).relIndex B ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_right]
      exact AddSubgroup.relIndex_ne_zero_trans hA0.1 hB.2.1
    refine ⟨A ⊓ B, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 ∅).2.1 A _ hA0 inf_le_left h1, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 B _ hB inf_le_right h2
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 A _ (hA i hi) inf_le_left h1

/- English proof (translation)
Introduce `W _ W0 ι s S h`. Take `⟨A, hA0, hA⟩` from `exists_common_goodSub W0 s S h`. Establish `himg : (QuotientAddGroup.mk : W → W ⧸ A) '' (⋃ i ∈ s, S i) = ⋃ i ∈ s, (QuotientAddGroup.mk : W → W ⧸ A) '' S i`. Simplify using `only [Set.image_iUnion]`. Establish `hU : GoodSub W0 A (⋃ i ∈ s, S i)`.

Use `⟨hA0.1, hA0.2.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx a ha`. Simplify using `only [Set.mem_iUnion] at hx ⊢`. Take `⟨i, hi, hx⟩` from `hx`. Conclude with `⟨i, hi, (hA i hi).2.2.1 x hx a ha⟩`.

Rewrite using `[himg]`. Conclude with `Set.Finite.biUnion s.finite_toSet fun i hi => (hA i hi).2.2.2`. Use `⟨⟨A, hU⟩, fun hd => ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).1 A hU, Finset.sum_congr rfl fun i hi => (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 (S i)).1 A (hA i hi), ← Finset.sum_mul, himg]`. Use `congr 1`.

Establish `key` using `Set.Finite.ncard_biUnion (t := (s : Set ι)) (s := fun i => (QuotientAddGroup.mk : W → W ⧸ A) '' S i) s.finite_toSet (fun i hi => (hA i hi).2.2.2) (by`. Introduce `i hi j hj hij`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩`. Establish `hm : -y + x ∈ A` using `QuotientAddGroup.eq.1 hxy`.

Use `(hA j hj).2.2.1 y hy _ hm` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`. Conclude with `Set.disjoint_left.1 (hd i hi j hj hij) hx this)`. Rewrite `key` using `[finsum_mem_coe_finset]`. Conclude with `key` after adjusting the coercions.
-/
theorem cont_biUnion : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type} (s : Finset ι) (S : ι → Set W), (∀ i ∈ s, IsCO W0 (S i)) → IsCO W0 (⋃ i ∈ s, S i) ∧ ((∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) → cont W0 (⋃ i ∈ s, S i) = ∑ i ∈ s, cont W0 (S i)) := by
  intro W _ W0 ι s S h
  obtain ⟨A, hA0, hA⟩ := exists_common_goodSub W0 s S h
  have himg : (QuotientAddGroup.mk : W → W ⧸ A) '' (⋃ i ∈ s, S i) =
      ⋃ i ∈ s, (QuotientAddGroup.mk : W → W ⧸ A) '' S i := by
    simp only [Set.image_iUnion]
  have hU : GoodSub W0 A (⋃ i ∈ s, S i) := by
    refine ⟨hA0.1, hA0.2.1, ?_, ?_⟩
    · intro x hx a ha
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨i, hi, (hA i hi).2.2.1 x hx a ha⟩
    · rw [himg]
      exact Set.Finite.biUnion s.finite_toSet fun i hi => (hA i hi).2.2.2
  refine ⟨⟨A, hU⟩, fun hd => ?_⟩
  rw [(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).1 A hU,
    Finset.sum_congr rfl fun i hi => (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 (S i)).1 A (hA i hi), ← Finset.sum_mul, himg]
  congr 1
  have key := Set.Finite.ncard_biUnion (t := (s : Set ι))
    (s := fun i => (QuotientAddGroup.mk : W → W ⧸ A) '' S i) s.finite_toSet
    (fun i hi => (hA i hi).2.2.2) (by
      intro i hi j hj hij
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hm : -y + x ∈ A := QuotientAddGroup.eq.1 hxy
      have := (hA j hj).2.2.1 y hy _ hm
      rw [add_neg_cancel_left] at this
      exact Set.disjoint_left.1 (hd i hi j hj hij) hx this)
  rw [finsum_mem_coe_finset] at key
  exact_mod_cast key

end GlobalTheory.HL
