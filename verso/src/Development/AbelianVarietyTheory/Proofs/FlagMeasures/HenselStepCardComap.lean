import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Establish `hsup : d.range ⊔ T2 = T1`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ h21` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hd1 w`.

Introduce `t ht`. Take `⟨w, hw⟩` from `hd2 t ht`. Establish `: t = d w + -(d w - t)` using `by abel`. Rewrite using `[this]`. Conclude with `AddSubgroup.add_mem_sup ⟨w, rfl⟩ (T2.neg_mem hw)`.

Establish `h1 : (T2.comap d).index = T2.relIndex T1`. Rewrite using `[AddSubgroup.index_comap, ← hsup, AddSubgroup.relIndex_sup_right]`. Establish `h2` using `AddSubgroup.card_mul_index (T2.comap d)`. Establish `h3` using `AddSubgroup.card_mul_index (T2.addSubgroupOf T1)`. Establish `h4 : Nat.card (T2.addSubgroupOf T1) = Nat.card T2` using `Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h21).toEquiv`.

Rewrite `h3` using `[h4]`. Rewrite using `[← h2, ← h3, h1]`. Unfold `AddSubgroup.relIndex`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem henselStep_card_comap {W T : Type} [AddCommGroup W] [AddCommGroup T]
    (T1 T2 : AddSubgroup T) (h21 : T2 ≤ T1) (d : W →+ T) (hd1 : ∀ w, d w ∈ T1)
    (hd2 : ∀ t ∈ T1, ∃ w, d w - t ∈ T2) :
    Nat.card (T2.comap d) * Nat.card T1 = Nat.card W * Nat.card T2 := by
  have hsup : d.range ⊔ T2 = T1 := by
    apply le_antisymm
    · refine sup_le ?_ h21
      rintro _ ⟨w, rfl⟩
      exact hd1 w
    · intro t ht
      obtain ⟨w, hw⟩ := hd2 t ht
      have : t = d w + -(d w - t) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup ⟨w, rfl⟩ (T2.neg_mem hw)
  have h1 : (T2.comap d).index = T2.relIndex T1 := by
    rw [AddSubgroup.index_comap, ← hsup, AddSubgroup.relIndex_sup_right]
  have h2 := AddSubgroup.card_mul_index (T2.comap d)
  have h3 := AddSubgroup.card_mul_index (T2.addSubgroupOf T1)
  have h4 : Nat.card (T2.addSubgroupOf T1) = Nat.card T2 :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h21).toEquiv
  rw [h4] at h3
  rw [← h2, ← h3, h1]
  unfold AddSubgroup.relIndex
  ring

/- English proof (translation)
Use `set S1 : Set V := {y | y ∈ P ∧ f y - τ ∈ T1} with hS1`. Use `set S2 : Set V := {y | y ∈ P ∧ f y - τ ∈ T2} with hS2`. Establish `ha : Nat.card (Σ y : S1, {w : W // (y : V) + ι w ∈ S2}) = S2.ncard * Nat.card W`. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_prod]`. Use `Nat.card_congr { toFun := fun p => (⟨p.1.1 + ι p.2.1, p.2.2⟩, p.2.1) invFun := fun q => ⟨⟨q.1.1 + ι (-q.2), ?_⟩, ⟨q.2, ?_⟩⟩ left_inv := ?_ right_inv := ?_ }` and prove the remaining obligations.

Take `⟨⟨u, hu, hu2⟩, w⟩` from `q`. Use `⟨hP u hu _, ?_⟩` and prove the remaining obligations. Take `⟨d, h1, -, h3⟩` from `hd u hu`. Establish `: f (u + ι (-w)) - τ = (f (u + ι (-w)) - f u - d (-w)) + d (-w) + (f u - τ)`. Normalize the expressions using the abelian group laws.

Simplify using `only`. Rewrite using `[this]`. Conclude with `T1.add_mem (T1.add_mem (h21 (h3 _)) (h1 _)) (h21 hu2)`. Simplify using the standard rewrite rules. Introduce and unpack `⟨⟨y, hy⟩, ⟨w, hw⟩⟩`.

Establish `: y + ι w + ι (-w) = y` using `by simp`. Use `Sigma.subtype_ext ?_ rfl` and prove the remaining obligations. Conclude with `Subtype.ext this`. Introduce and unpack `⟨⟨u, hu⟩, w⟩`. Simplify using the standard rewrite rules.

Establish `hb : ∀ y : S1, Nat.card {w : W // (y : V) + ι w ∈ S2} * Nat.card T1 = Nat.card W * Nat.card T2`. Introduce and unpack `⟨y, hy, hy1⟩`. Take `⟨d, h1, h2, h3⟩` from `hd y hy`. Rewrite using `[← henselStep_card_comap T1 T2 h21 d h1 h2]`. Use `congr 1`.

Take `⟨w0, hw0⟩` from `h2 _ (T1.neg_mem hy1)`. Use `Nat.card_congr ((Equiv.subRight w0).subtypeEquiv ?_)` and prove the remaining obligations. Introduce `w`. Simplify using `only [hS2, Set.mem_setOf_eq, Equiv.subRight_apply, AddSubgroup.mem_comap, map_sub]`. Establish `key : f (y + ι w) - τ = (f (y + ι w) - f y - d w) + (d w0 - -(f y - τ)) + (d w - d w0)` using `by abel`.

Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Conclude with `(T2.add_mem_cancel_left (T2.add_mem (h3 w) hw0)).1 h`. Introduce `h`.

Conclude with `⟨hP y hy w, T2.add_mem (T2.add_mem (h3 w) hw0) h⟩`. Use `haveI := Fintype.ofFinite S1`. Rewrite `ha` using `[Nat.card_sigma]`. Establish `hc : S2.ncard * Nat.card W * Nat.card T1 = S1.ncard * (Nat.card W * Nat.card T2)`. Rewrite using `[← ha, Finset.sum_mul, Finset.sum_congr rfl (fun y _ => hb y), Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]`.

Establish `hW : 0 < Nat.card W` using `Nat.card_pos`. Apply `Nat.eq_of_mul_eq_mul_left hW` to reduce the goal to its premises. Combine the linear relations using `[hc]`.
-/
theorem henselStep_count {V W T : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Finite V] [Finite W] [Finite T] (ι : W →+ V) (f : V → T) (P : Set V)
    (T1 T2 : AddSubgroup T) (τ : T) (h21 : T2 ≤ T1) (hP : ∀ y ∈ P, ∀ w, y + ι w ∈ P)
    (hd : ∀ y ∈ P, ∃ d : W →+ T, (∀ w, d w ∈ T1) ∧ (∀ t ∈ T1, ∃ w, d w - t ∈ T2) ∧
      ∀ w, f (y + ι w) - f y - d w ∈ T2) :
    Set.ncard {y | y ∈ P ∧ f y - τ ∈ T1} * Nat.card T2 =
      Set.ncard {y | y ∈ P ∧ f y - τ ∈ T2} * Nat.card T1 := by
  set S1 : Set V := {y | y ∈ P ∧ f y - τ ∈ T1} with hS1
  set S2 : Set V := {y | y ∈ P ∧ f y - τ ∈ T2} with hS2

  have ha : Nat.card (Σ y : S1, {w : W // (y : V) + ι w ∈ S2}) = S2.ncard * Nat.card W := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun p => (⟨p.1.1 + ι p.2.1, p.2.2⟩, p.2.1)
        invFun := fun q => ⟨⟨q.1.1 + ι (-q.2), ?_⟩, ⟨q.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨⟨u, hu, hu2⟩, w⟩ := q
      refine ⟨hP u hu _, ?_⟩
      obtain ⟨d, h1, -, h3⟩ := hd u hu
      have : f (u + ι (-w)) - τ = (f (u + ι (-w)) - f u - d (-w)) + d (-w) + (f u - τ) := by
        abel
      simp only
      rw [this]
      exact T1.add_mem (T1.add_mem (h21 (h3 _)) (h1 _)) (h21 hu2)
    · simp
    · rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
      have : y + ι w + ι (-w) = y := by simp
      refine Sigma.subtype_ext ?_ rfl
      exact Subtype.ext this
    · rintro ⟨⟨u, hu⟩, w⟩
      simp
  have hb : ∀ y : S1, Nat.card {w : W // (y : V) + ι w ∈ S2} * Nat.card T1 =
      Nat.card W * Nat.card T2 := by
    rintro ⟨y, hy, hy1⟩
    obtain ⟨d, h1, h2, h3⟩ := hd y hy
    rw [← henselStep_card_comap T1 T2 h21 d h1 h2]
    congr 1
    obtain ⟨w0, hw0⟩ := h2 _ (T1.neg_mem hy1)
    refine Nat.card_congr ((Equiv.subRight w0).subtypeEquiv ?_)
    intro w
    simp only [hS2, Set.mem_setOf_eq, Equiv.subRight_apply, AddSubgroup.mem_comap, map_sub]
    have key : f (y + ι w) - τ =
        (f (y + ι w) - f y - d w) + (d w0 - -(f y - τ)) + (d w - d w0) := by abel
    rw [key]
    constructor
    · rintro ⟨-, h⟩
      exact (T2.add_mem_cancel_left (T2.add_mem (h3 w) hw0)).1 h
    · intro h
      exact ⟨hP y hy w, T2.add_mem (T2.add_mem (h3 w) hw0) h⟩
  haveI := Fintype.ofFinite S1
  rw [Nat.card_sigma] at ha
  have hc : S2.ncard * Nat.card W * Nat.card T1 = S1.ncard * (Nat.card W * Nat.card T2) := by
    rw [← ha, Finset.sum_mul, Finset.sum_congr rfl (fun y _ => hb y), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hW : 0 < Nat.card W := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hW
  linarith [hc]

end GlobalTheory
