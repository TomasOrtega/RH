import Mathlib
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Take `⟨ι, x, hx⟩` from `exists_isTranscendenceBasis' K₀ K₂`. Rewrite using `[← hx.cardinalMk_eq_trdeg]`. Set `E` to `IntermediateField.adjoin K₁ (Set.range fun i => φ (x i))`. Establish `hm : ∀ a ∈ Algebra.adjoin K₀ (Set.range x), φ a ∈ E`. Introduce `a ha`.

Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Take `⟨i, rfl⟩` from `ha`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩`. Consider the case `algebraMap r`.

Establish `h : φ (algebraMap K₀ K₂ r) = algebraMap K₁ L (algebraMap K₀ K₁ r)` using `RingHom.congr_fun hφ r`. Rewrite using `[h]`. Conclude with `E.algebraMap_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`. Establish `halg : ∀ f, IsAlgebraic E (φ f)`. Introduce `f`. Establish `hf : IsAlgebraic (Algebra.adjoin K₀ (Set.range x)) f` using `hx.isAlgebraic.isAlgebraic f`.

Set `g : Algebra.adjoin K₀ (Set.range x) →+* E` to `(φ.comp (Algebra.adjoin K₀ (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2`. Establish `hg : Function.Injective g` using `fun a b h => Subtype.ext (φ.injective (congrArg Subtype.val h))`. Conclude with `hf.ringHom_of_comp_eq g φ hg rfl`. Establish `hL : Algebra.IsAlgebraic E L`. Use `⟨fun z => ?_⟩` and prove the remaining obligations.

Establish `hle : Subfield.closure (Set.range (algebraMap K₁ L) ∪ Set.range φ) ≤ (algebraicClosure E L).toSubfield`. Use `Subfield.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨k, rfl⟩ | ⟨f, rfl⟩)`. Conclude with `(algebraicClosure E L).algebraMap_mem (algebraMap K₁ E k)`. Conclude with `mem_algebraicClosure_iff.2 (halg f)`.

Rewrite `hle` using `[hcl]`. Conclude with `mem_algebraicClosure_iff.1 (hle (Subfield.mem_top z))`. Establish `hE : Algebra.trdeg K₁ E ≤ Cardinal.mk ι`. Establish `: Algebra.IsAlgebraic (Algebra.adjoin K₁ (Set.range fun i => (⟨φ (x i), IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E`. Rewrite using `[← IntermediateField.isAlgebraic_adjoin_iff_top]`.

Establish `htop : IntermediateField.adjoin K₁ (Set.range fun i => (⟨φ (x i), IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤`. Apply `IntermediateField.lift_injective` to reduce the goal to its premises. Rewrite using `[IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[htop]`.

Use `infer_instance`. Conclude with `(Algebra.IsAlgebraic.trdeg_le_cardinalMk K₁ _ (alg := this)).trans Cardinal.mk_range_le`. Use `haveI : FaithfulSMul E L := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E L).injective`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← trdeg_add_eq K₁ E (A := L), trdeg_eq_zero (R := E) (A := L), add_zero]`.

Use `_ ≤ _ := hE`.
-/
theorem trdeg_le_of_closure_range_union_eq_top (K₀ K₁ K₂ L : Type) [Field K₀] [Field K₁] [Field K₂]
    [Field L] [Algebra K₀ K₁] [Algebra K₀ K₂] [Algebra K₁ L] (φ : K₂ →+* L)
    (hφ : φ.comp (algebraMap K₀ K₂) = (algebraMap K₁ L).comp (algebraMap K₀ K₁))
    (hcl : Subfield.closure (Set.range (algebraMap K₁ L) ∪ Set.range φ) = ⊤) :
    Algebra.trdeg K₁ L ≤ Algebra.trdeg K₀ K₂ := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K₀ K₂
  rw [← hx.cardinalMk_eq_trdeg]
  let E := IntermediateField.adjoin K₁ (Set.range fun i => φ (x i))
  have hm : ∀ a ∈ Algebra.adjoin K₀ (Set.range x), φ a ∈ E := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r =>
      have h : φ (algebraMap K₀ K₂ r) = algebraMap K₁ L (algebraMap K₀ K₁ r) :=
        RingHom.congr_fun hφ r
      rw [h]
      exact E.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have halg : ∀ f, IsAlgebraic E (φ f) := by
    intro f
    have hf : IsAlgebraic (Algebra.adjoin K₀ (Set.range x)) f := hx.isAlgebraic.isAlgebraic f
    let g : Algebra.adjoin K₀ (Set.range x) →+* E :=
      (φ.comp (Algebra.adjoin K₀ (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
    have hg : Function.Injective g := fun a b h =>
      Subtype.ext (φ.injective (congrArg Subtype.val h))
    exact hf.ringHom_of_comp_eq g φ hg rfl
  have hL : Algebra.IsAlgebraic E L := by
    refine ⟨fun z => ?_⟩
    have hle : Subfield.closure (Set.range (algebraMap K₁ L) ∪ Set.range φ) ≤
        (algebraicClosure E L).toSubfield := by
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨k, rfl⟩ | ⟨f, rfl⟩)
      · exact (algebraicClosure E L).algebraMap_mem (algebraMap K₁ E k)
      · exact mem_algebraicClosure_iff.2 (halg f)
    rw [hcl] at hle
    exact mem_algebraicClosure_iff.1 (hle (Subfield.mem_top z))
  have hE : Algebra.trdeg K₁ E ≤ Cardinal.mk ι := by
    have : Algebra.IsAlgebraic (Algebra.adjoin K₁ (Set.range fun i => (⟨φ (x i),
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E := by
      rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
      have htop : IntermediateField.adjoin K₁ (Set.range fun i => (⟨φ (x i),
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤ := by
        apply IntermediateField.lift_injective
        rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
        rfl
      rw [htop]
      infer_instance
    exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk K₁ _ (alg := this)).trans Cardinal.mk_range_le
  haveI : FaithfulSMul E L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E L).injective
  calc Algebra.trdeg K₁ L = Algebra.trdeg K₁ E := by
        rw [← trdeg_add_eq K₁ E (A := L), trdeg_eq_zero (R := E) (A := L), add_zero]
    _ ≤ _ := hE

end GlobalTheory
