import Mathlib

namespace GlobalTheory.DenseEmbeddingProduct

open NumberField NumberField.InfinitePlace

/- English proof (translation)
Set `Φ : InfiniteAdeleRing E → (InfinitePlace E → ℂ)` to `fun y w ↦ Completion.extensionEmbedding w (y w)`. Establish `hc : Continuous Φ` using `continuous_pi fun w ↦ (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)`. Establish `hs : Function.Surjective Φ`. Introduce `f`. Use `choose y hy using fun w : InfinitePlace E ↦ Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (f w)`.

Conclude with `⟨y, funext hy⟩`. Establish `h` using `hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x w`. Simplify using `[Φ]`.
-/
theorem denseRange_embedding_pi {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DenseRange fun (x : E) (w : InfinitePlace E) ↦ (InfinitePlace.embedding w : E → ℂ) x := by
  let Φ : InfiniteAdeleRing E → (InfinitePlace E → ℂ) :=
    fun y w ↦ Completion.extensionEmbedding w (y w)
  have hc : Continuous Φ := continuous_pi fun w ↦
    (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have hs : Function.Surjective Φ := by
    intro f
    choose y hy using fun w : InfinitePlace E ↦
      Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (f w)
    exact ⟨y, funext hy⟩
  have h := hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc
  convert h using 1
  funext x w
  simp [Φ]

end GlobalTheory.DenseEmbeddingProduct
