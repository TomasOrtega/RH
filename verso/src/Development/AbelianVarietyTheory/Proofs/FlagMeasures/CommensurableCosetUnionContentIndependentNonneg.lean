import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Use extensionality with `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H x`. Establish `h1 : (AddSubgroup.quotientEquivProdOfLE hle (QuotientAddGroup.mk x)).1 = (QuotientAddGroup.mk x : W ⧸ A)` using `rfl`. Simplify using `only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, h1]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `⟨y, hy, QuotientAddGroup.eq.2 (hle (QuotientAddGroup.eq.1 hyx))⟩`. Introduce and unpack `⟨y, hy, hyx⟩`. Use `hS y hy _ (QuotientAddGroup.eq.1 hyx)` as an intermediate fact.

Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Simplify using `using this`.
-/
theorem image_mk_eq_preimage_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    (QuotientAddGroup.mk : W → W ⧸ A') '' S =
      (AddSubgroup.quotientEquivProdOfLE hle) ⁻¹'
        (((QuotientAddGroup.mk : W → W ⧸ A) '' S) ×ˢ Set.univ) := by
  ext q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    have h1 : (AddSubgroup.quotientEquivProdOfLE hle (QuotientAddGroup.mk x)).1 =
        (QuotientAddGroup.mk x : W ⧸ A) := rfl
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, h1]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, QuotientAddGroup.eq.2 (hle (QuotientAddGroup.eq.1 hyx))⟩
    · rintro ⟨y, hy, hyx⟩
      have := hS y hy _ (QuotientAddGroup.eq.1 hyx)
      refine ⟨x, ?_, rfl⟩
      simpa using this

/- English proof (translation)
Rewrite using `[image_mk_eq_preimage_of_le hle hS, Set.ncard_preimage_of_injective_subset_range (Equiv.injective _) (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), Set.ncard_prod, Set.ncard_univ]`. Both sides reduce to the same expression.
-/
theorem ncard_image_mk_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * A'.relIndex A := by
  rw [image_mk_eq_preimage_of_le hle hS,
    Set.ncard_preimage_of_injective_subset_range (Equiv.injective _)
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), Set.ncard_prod, Set.ncard_univ]
  rfl

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `h`. Use `⟨AddSubgroup.relIndex_ne_zero_trans hi h1, fun h0 => h2 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0), fun x hx a ha => h3 x hx a (hle ha), ?_⟩` and prove the remaining obligations. Rewrite using `[image_mk_eq_preimage_of_le hle h3]`. Use `haveI : Finite (A ⧸ A'.addSubgroupOf A) := Nat.finite_of_card_ne_zero hi`. Conclude with `(h4.prod Set.finite_univ).preimage (Equiv.injective _).injOn`.
-/
theorem GoodSub.of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) : GoodSub W0 A' S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨AddSubgroup.relIndex_ne_zero_trans hi h1,
    fun h0 => h2 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    fun x hx a ha => h3 x hx a (hle ha), ?_⟩
  rw [image_mk_eq_preimage_of_le hle h3]
  haveI : Finite (A ⧸ A'.addSubgroupOf A) := Nat.finite_of_card_ne_zero hi
  exact (h4.prod Set.finite_univ).preimage (Equiv.injective _).injOn

/- English proof (translation)
Establish `h1' : A'.relIndex W0 ≠ 0` using `AddSubgroup.relIndex_ne_zero_trans hi h1`. Establish `e1 : W0.relIndex A' * A'.relIndex A = (W0 ⊓ A').relIndex A`. Use `AddSubgroup.relIndex_inf_mul_relIndex W0 A' A` as an intermediate fact. Rewrite `this` using `[inf_eq_left.2 hle]`. Then use the resulting hypothesis. Establish `e2 : A'.relIndex (W0 ⊓ A) * W0.relIndex A = (A' ⊓ W0).relIndex A` using `AddSubgroup.relIndex_inf_mul_relIndex A' W0 A`.

Establish `e3 : A'.relIndex (A ⊓ W0) * A.relIndex W0 = A'.relIndex W0`. Use `AddSubgroup.relIndex_inf_mul_relIndex A' A W0` as an intermediate fact. Rewrite `this` using `[inf_eq_left.2 hle]`. Then use the resulting hypothesis. Rewrite `e2` using `[inf_comm A' W0, ← e1, inf_comm W0 A]`. Establish `e2' : (A'.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = W0.relIndex A' * A'.relIndex A`.

Conclude with `e2` after adjusting the coercions. Establish `e3' : (A'.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = A'.relIndex W0`. Conclude with `e3` after adjusting the coercions. Establish `n1 : (A.relIndex W0 : ℝ) ≠ 0` using `by exact_mod_cast h1`. Establish `n2 : (A'.relIndex W0 : ℝ) ≠ 0` using `by exact_mod_cast h1'`.

Unfold `relVol`. Rewrite using `[← mul_div_assoc, div_eq_div_iff n1 n2, ← e3']`. Take the linear combination `(A.relIndex W0 : ℝ) * e2'`.
-/
theorem relVol_eq_mul_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    relVol W0 A = (A'.relIndex A : ℝ) * relVol W0 A' := by
  have h1' : A'.relIndex W0 ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hi h1
  have e1 : W0.relIndex A' * A'.relIndex A = (W0 ⊓ A').relIndex A := by
    have := AddSubgroup.relIndex_inf_mul_relIndex W0 A' A
    rwa [inf_eq_left.2 hle] at this
  have e2 : A'.relIndex (W0 ⊓ A) * W0.relIndex A = (A' ⊓ W0).relIndex A :=
    AddSubgroup.relIndex_inf_mul_relIndex A' W0 A
  have e3 : A'.relIndex (A ⊓ W0) * A.relIndex W0 = A'.relIndex W0 := by
    have := AddSubgroup.relIndex_inf_mul_relIndex A' A W0
    rwa [inf_eq_left.2 hle] at this
  rw [inf_comm A' W0, ← e1, inf_comm W0 A] at e2
  have e2' : (A'.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = W0.relIndex A' * A'.relIndex A := by
    exact_mod_cast e2
  have e3' : (A'.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = A'.relIndex W0 := by
    exact_mod_cast e3
  have n1 : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1
  have n2 : (A'.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1'
  unfold relVol
  rw [← mul_div_assoc, div_eq_div_iff n1 n2, ← e3']
  linear_combination (A.relIndex W0 : ℝ) * e2'

/- English proof (translation)
Rewrite using `[ncard_image_mk_of_le hle h.2.2.1, relVol_eq_mul_of_le h.1 hle hi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GoodSub.count_eq_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard : ℝ) * relVol W0 A' := by
  rw [ncard_image_mk_of_le hle h.2.2.1, relVol_eq_mul_of_le h.1 hle hi]
  push_cast
  ring

/- English proof (translation)
Establish `i1 : (A ⊓ B).relIndex A ≠ 0`. Rewrite using `[AddSubgroup.inf_relIndex_left]`. Conclude with `AddSubgroup.relIndex_ne_zero_trans hB.1 hA.2.1`. Establish `i2 : (A ⊓ B).relIndex B ≠ 0`. Rewrite using `[AddSubgroup.inf_relIndex_right]`.

Conclude with `AddSubgroup.relIndex_ne_zero_trans hA.1 hB.2.1`. Rewrite using `[hA.count_eq_of_le inf_le_left i1, hB.count_eq_of_le inf_le_right i2]`.
-/
theorem GoodSub.count_eq {W : Type} [AddCommGroup W] {W0 A B : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) (hB : GoodSub W0 B S) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard : ℝ) * relVol W0 B := by
  have i1 : (A ⊓ B).relIndex A ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_left]
    exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA.2.1
  have i2 : (A ⊓ B).relIndex B ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_ne_zero_trans hA.1 hB.2.1
  rw [hA.count_eq_of_le inf_le_left i1, hB.count_eq_of_le inf_le_right i2]

/- English proof (translation)
Establish `h : IsCO W0 S` using `⟨A, hA⟩`. Unfold `cont`. Rewrite using `[dif_pos h]`. Conclude with `GoodSub.count_eq h.choose_spec hA`.
-/
theorem GoodSub.cont_eq {W : Type} [AddCommGroup W] {W0 A : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) :
    cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A := by
  have h : IsCO W0 S := ⟨A, hA⟩
  unfold cont
  rw [dif_pos h]
  exact GoodSub.count_eq h.choose_spec hA

/- English proof (translation)
Introduce `W _ W0 S`. Use `⟨fun A hA => hA.cont_eq, fun A A' h hle hi => h.of_le hle hi, ?_, ?_⟩` and prove the remaining obligations. Unfold `cont relVol split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.

Introduce and unpack `⟨A, hA⟩ hne`. Rewrite using `[hA.cont_eq]`. Establish `p1 : 0 < ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard` using `(Set.ncard_pos hA.2.2.2).2 (hne.image _)`. Establish `p2 : 0 < W0.relIndex A` using `Nat.pos_of_ne_zero hA.2.1`. Establish `p3 : 0 < A.relIndex W0` using `Nat.pos_of_ne_zero hA.1`.

Unfold `relVol`. Check the signs of the components of the expression.
-/
theorem cont_independent_pos : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  intro W _ W0 S
  refine ⟨fun A hA => hA.cont_eq, fun A A' h hle hi => h.of_le hle hi, ?_, ?_⟩
  · unfold cont relVol
    split_ifs
    · positivity
    · exact le_rfl
  · rintro ⟨A, hA⟩ hne
    rw [hA.cont_eq]
    have p1 : 0 < ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard :=
      (Set.ncard_pos hA.2.2.2).2 (hne.image _)
    have p2 : 0 < W0.relIndex A := Nat.pos_of_ne_zero hA.2.1
    have p3 : 0 < A.relIndex W0 := Nat.pos_of_ne_zero hA.1
    unfold relVol
    positivity

end GlobalTheory.HL
