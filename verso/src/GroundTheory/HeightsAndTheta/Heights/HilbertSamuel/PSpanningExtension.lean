import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module Set

/- English proof (translation)
Introduce `V _ _ _ ι _ v S hv hS`. Use `set s : Set V := range v with hs_def`. Establish `hs : LinearIndepOn ℝ id s` using `(linearIndepOn_id_range_iff hv.injective).mpr hv`. Establish `hst : s ⊆ s ∪ S` using `subset_union_left`. Use `set b := hs.extend hst with hb_def`.

Establish `hsb : s ⊆ b` using `hs.subset_extend hst`. Establish `hbt : b ⊆ s ∪ S` using `hs.extend_subset hst`. Establish `hbli : LinearIndependent ℝ (fun x : b => (x : V))` using `hs.linearIndepOn_extend hst`. Establish `hspan : ⊤ ≤ Submodule.span ℝ (range (fun x : b => (x : V)))`. Rewrite using `[Subtype.range_coe, ← hS]`.

Conclude with `Submodule.span_le.2 (subset_union_right.trans (hs.subset_span_extend hst))`. Set `B` to `Basis.mk hbli hspan`. Establish `hcard_b : Nat.card b = finrank ℝ V` using `(finrank_eq_nat_card_basis B).symm`. Establish `: Finite b` using `Module.Finite.finite_basis B`. Establish `hbfin : b.Finite` using `toFinite b`.

Establish `hcard_s : s.ncard = Fintype.card ι`. Rewrite using `[hs_def, ncard_range_of_injective hv.injective, Nat.card_eq_fintype_card]`. Establish `hk : Nat.card (b \ s : Set V) = finrank ℝ V - Fintype.card ι`. Rewrite using `[Nat.card_coe_set_eq, ncard_sdiff hsb (hbfin.subset hsb), ← hcard_s, ← Nat.card_coe_set_eq, hcard_b]`. Set `e : (b \ s : Set V) ≃ Fin (finrank ℝ V - Fintype.card ι)` to `Finite.equivFinOfCardEq hk`.

Set `w : Fin (finrank ℝ V - Fintype.card ι) → V` to `fun j => (e.symm j : V)`. Establish `hw_mem : ∀ j, w j ∈ b \ s` using `fun j => (e.symm j).2`. Use `⟨w, fun j => ?_, ?_⟩` and prove the remaining obligations. Take `⟨hb, hns⟩` from `hw_mem j`. Break down `hbt hb with h | h` into its components or cases.

Conclude with `absurd h hns`. Conclude with `h`. Set `f : ι ⊕ Fin (finrank ℝ V - Fintype.card ι) → b` to `Sum.elim (fun i => ⟨v i, hsb (mem_range_self i)⟩) (fun j => ⟨w j, (hw_mem j).1⟩)`. Establish `hf : Function.Injective f`. Apply the tactic sequence `rintro (i | j) (i' | j') h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h`.

Rewrite using `[hv.injective h]`. Conclude with `absurd (h ▸ mem_range_self i) (hw_mem j').2`. Conclude with `absurd (h ▸ mem_range_self i') (hw_mem j).2`. Rewrite using `[e.symm.injective (Subtype.ext h)]`. Establish `: Sum.elim v w = (fun x : b => (x : V)) ∘ f`.

Apply the tactic sequence `funext x; rcases x with i | j <;> rfl`. Rewrite using `[this]`. Conclude with `hbli.comp f hf`.
-/
theorem SpanningExtension.proof : SpanningExtension.Statement := by
  intro V _ _ _ ι _ v S hv hS
  classical
  set s : Set V := range v with hs_def
  have hs : LinearIndepOn ℝ id s := (linearIndepOn_id_range_iff hv.injective).mpr hv
  have hst : s ⊆ s ∪ S := subset_union_left
  set b := hs.extend hst with hb_def
  have hsb : s ⊆ b := hs.subset_extend hst
  have hbt : b ⊆ s ∪ S := hs.extend_subset hst
  have hbli : LinearIndependent ℝ (fun x : b => (x : V)) := hs.linearIndepOn_extend hst
  have hspan : ⊤ ≤ Submodule.span ℝ (range (fun x : b => (x : V))) := by
    rw [Subtype.range_coe, ← hS]
    exact Submodule.span_le.2 (subset_union_right.trans (hs.subset_span_extend hst))
  let B := Basis.mk hbli hspan
  have hcard_b : Nat.card b = finrank ℝ V := (finrank_eq_nat_card_basis B).symm
  have : Finite b := Module.Finite.finite_basis B
  have hbfin : b.Finite := toFinite b
  have hcard_s : s.ncard = Fintype.card ι := by
    rw [hs_def, ncard_range_of_injective hv.injective, Nat.card_eq_fintype_card]
  have hk : Nat.card (b \ s : Set V) = finrank ℝ V - Fintype.card ι := by
    rw [Nat.card_coe_set_eq, ncard_sdiff hsb (hbfin.subset hsb), ← hcard_s, ← Nat.card_coe_set_eq,
      hcard_b]
  let e : (b \ s : Set V) ≃ Fin (finrank ℝ V - Fintype.card ι) := Finite.equivFinOfCardEq hk
  let w : Fin (finrank ℝ V - Fintype.card ι) → V := fun j => (e.symm j : V)
  have hw_mem : ∀ j, w j ∈ b \ s := fun j => (e.symm j).2
  refine ⟨w, fun j => ?_, ?_⟩
  · obtain ⟨hb, hns⟩ := hw_mem j
    rcases hbt hb with h | h
    · exact absurd h hns
    · exact h
  · let f : ι ⊕ Fin (finrank ℝ V - Fintype.card ι) → b :=
      Sum.elim (fun i => ⟨v i, hsb (mem_range_self i)⟩) (fun j => ⟨w j, (hw_mem j).1⟩)
    have hf : Function.Injective f := by
      rintro (i | j) (i' | j') h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      · rw [hv.injective h]
      · exact absurd (h ▸ mem_range_self i) (hw_mem j').2
      · exact absurd (h ▸ mem_range_self i') (hw_mem j).2
      · rw [e.symm.injective (Subtype.ext h)]
    have : Sum.elim v w = (fun x : b => (x : V)) ∘ f := by
      funext x; rcases x with i | j <;> rfl
    rw [this]
    exact hbli.comp f hf

end GroundTheory.Heights₂.Heights.HilbertSamuel
