import Mathlib

namespace GlobalTheory.EmbeddingRangeSpanTop

open NumberField

/- English proof (translation)
Set `L : NumberField.mixedEmbedding.mixedSpace F →ₗ[ℝ] (NumberField.InfinitePlace F → ℂ)` to `{ toFun := fun x v => x.2 ⟨v, NumberField.IsTotallyComplex.isComplex v⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hL : Function.Surjective L` using `fun z => ⟨(0, fun w => z w.1), rfl⟩`. Establish `hcomp : (fun (a : F) (v : NumberField.InfinitePlace F) ↦ (NumberField.InfinitePlace.embedding v : F → ℂ) a) = L ∘ (NumberField.mixedEmbedding F)`. Use function extensionality and compare the values at `a v`. Simplify using `[L, NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]`.

Establish `hspan : Submodule.span ℝ (Set.range (NumberField.mixedEmbedding F)) = ⊤`. Rewrite using `[eq_top_iff, ← (NumberField.mixedEmbedding.latticeBasis F).span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨_, (NumberField.mixedEmbedding.latticeBasis_apply F i).symm⟩`.

Rewrite using `[hcomp, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `hL`.
-/
theorem span_range_embedding_eq_top (F : Type) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : NumberField.InfinitePlace F) ↦
      (NumberField.InfinitePlace.embedding v : F → ℂ) a) = ⊤ := by
  classical
  let L : NumberField.mixedEmbedding.mixedSpace F →ₗ[ℝ] (NumberField.InfinitePlace F → ℂ) :=
    { toFun := fun x v => x.2 ⟨v, NumberField.IsTotallyComplex.isComplex v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Surjective L := fun z => ⟨(0, fun w => z w.1), rfl⟩
  have hcomp : (fun (a : F) (v : NumberField.InfinitePlace F) ↦
      (NumberField.InfinitePlace.embedding v : F → ℂ) a) = L ∘ (NumberField.mixedEmbedding F) := by
    funext a v
    simp [L, NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hspan : Submodule.span ℝ (Set.range (NumberField.mixedEmbedding F)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.mixedEmbedding.latticeBasis F).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (NumberField.mixedEmbedding.latticeBasis_apply F i).symm⟩
  rw [hcomp, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact hL

end GlobalTheory.EmbeddingRangeSpanTop
