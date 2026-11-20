import Mathlib

noncomputable section

namespace PI.OmLocU

open MeasureTheory

/- English proof (translation)
Use `set H' := H.addSubgroupOf L with hH'`. Use `haveI : H'.FiniteIndex := ⟨hfin⟩`. Use `set T : Set (L ⧸ H') := QuotientAddGroup.mk '' S with hT`. Establish `hTfin : T.Finite` using `Set.toFinite T`. Establish `hr : ∀ t ∈ T, ∃ x ∈ S, (QuotientAddGroup.mk x : L ⧸ H') = t` using `fun t ht => ht`.

Use `choose! r hrS hrt using hr`. Set `C : L ⧸ H' → Set V` to `fun t => (fun v => -((r t : L) : V) + v) ⁻¹' (H : Set V)`. Establish `hCm : ∀ t, MeasurableSet (C t)` using `fun t => measurable_const_add _ hH`. Establish `hCμ : ∀ t, μ (C t) = μ H` using `fun t => measure_preimage_add μ _ _`. Establish `hU : ((↑) : L → V) '' S = ⋃ t ∈ hTfin.toFinset, C t`.

Use extensionality with `v`. Simplify using `only [Set.mem_image, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨QuotientAddGroup.mk x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `e` using `hrt _ ⟨x, hx, rfl⟩`. Rewrite `e` using `[QuotientAddGroup.eq]`. Establish `e' : ((-(r (QuotientAddGroup.mk x)) + x : L) : V) ∈ H` using `e`. Simplify `e'` using `[C]`. Introduce and unpack `⟨t, ht, hv⟩`.

Establish `hvH : -((r t : L) : V) + v ∈ H` using `hv`. Use `⟨r t + ⟨-((r t : L) : V) + v, hHL hvH⟩, hS _ (hrS t ht) _ hvH, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[hU, measure_biUnion_finset]`. Simplify using `only [hCμ, Finset.sum_const, nsmul_eq_mul]`.

Use `congr 1`. Rewrite using `[Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card T hTfin]`. Introduce `t ht t' ht' hne`. Establish `ht1 : t ∈ T` using `hTfin.mem_toFinset.mp ht`. Establish `ht2 : t' ∈ T` using `hTfin.mem_toFinset.mp ht'`.

Use `Set.disjoint_left.mpr fun v hv hv' => hne ?_` and prove the remaining obligations. Rewrite using `[← hrt t ht1, ← hrt t' ht2, QuotientAddGroup.eq]`. Use `show ((-(r t) + r t' : L) : V) ∈ H`. Establish `hs` using `H.sub_mem (show -((r t : L) : V) + v ∈ H from hv) (show -((r t' : L) : V) + v ∈ H from hv')`. Use `hs using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Normalize the expressions using the abelian group laws. Conclude with `fun t _ => hCm t`.
-/
theorem measure_image_cosets {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (H L : AddSubgroup V) (hHL : H ≤ L)
    (hH : MeasurableSet (H : Set V)) (hfin : H.relIndex L ≠ 0) (S : Set L)
    (hS : ∀ x ∈ S, ∀ y : L, (y : V) ∈ H → x + y ∈ S) :
    μ (((↑) : L → V) '' S) =
      (Nat.card (QuotientAddGroup.mk '' S : Set (L ⧸ H.addSubgroupOf L)) : ENNReal) * μ H := by
  classical
  set H' := H.addSubgroupOf L with hH'
  haveI : H'.FiniteIndex := ⟨hfin⟩
  set T : Set (L ⧸ H') := QuotientAddGroup.mk '' S with hT
  have hTfin : T.Finite := Set.toFinite T
  have hr : ∀ t ∈ T, ∃ x ∈ S, (QuotientAddGroup.mk x : L ⧸ H') = t := fun t ht => ht
  choose! r hrS hrt using hr
  let C : L ⧸ H' → Set V := fun t => (fun v => -((r t : L) : V) + v) ⁻¹' (H : Set V)
  have hCm : ∀ t, MeasurableSet (C t) := fun t => measurable_const_add _ hH
  have hCμ : ∀ t, μ (C t) = μ H := fun t => measure_preimage_add μ _ _
  have hU : ((↑) : L → V) '' S = ⋃ t ∈ hTfin.toFinset, C t := by
    ext v
    simp only [Set.mem_image, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨QuotientAddGroup.mk x, ⟨x, hx, rfl⟩, ?_⟩
      have e := hrt _ ⟨x, hx, rfl⟩
      rw [QuotientAddGroup.eq] at e
      have e' : ((-(r (QuotientAddGroup.mk x)) + x : L) : V) ∈ H := e
      simpa [C] using e'
    · rintro ⟨t, ht, hv⟩
      have hvH : -((r t : L) : V) + v ∈ H := hv
      refine ⟨r t + ⟨-((r t : L) : V) + v, hHL hvH⟩, hS _ (hrS t ht) _ hvH, ?_⟩
      simp
  rw [hU, measure_biUnion_finset]
  · simp only [hCμ, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card T hTfin]
  · intro t ht t' ht' hne
    have ht1 : t ∈ T := hTfin.mem_toFinset.mp ht
    have ht2 : t' ∈ T := hTfin.mem_toFinset.mp ht'
    refine Set.disjoint_left.mpr fun v hv hv' => hne ?_
    rw [← hrt t ht1, ← hrt t' ht2, QuotientAddGroup.eq]
    show ((-(r t) + r t' : L) : V) ∈ H
    have hs := H.sub_mem (show -((r t : L) : V) + v ∈ H from hv) (show -((r t' : L) : V) + v ∈ H from hv')
    convert hs using 1
    push_cast
    abel
  · exact fun t _ => hCm t

end PI.OmLocU
