import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.UnitsDense

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `h1` using `NumberField.InfiniteAdeleRing.denseRange_algebraMap E`. Establish `hs : Function.Surjective (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w)`. Introduce `y`. Use `choose x hx using fun w : InfinitePlace E => InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)`. Conclude with `⟨x, funext hx⟩`.

Establish `hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w)` using `continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)`. Use `hs.denseRange.comp h1 hc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x w`. Express the relevant statement in the definitionally equal form `w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)`.

Rewrite using `[InfiniteAdeleRing.algebraMap_apply]`. Use `InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)` as an intermediate fact. Simplify using `only [RingEquiv.apply_symm_apply] at this`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem denseRange_embeddings' : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

/- English proof (translation)
Introduce `E _ _ _ V hV ⟨v, hv⟩`. Establish `hU : IsOpen (Units.val '' V)` using `Units.isOpenEmbedding_val.isOpenMap V hV`. Establish `hd : DenseRange fun x : E => pInf E (algebraMap E (Ad E) x)`. Establish `: (fun x : E => pInf E (algebraMap E (Ad E) x)) = fun (x : E) (w : InfinitePlace E) => w.embedding x`. Use function extensionality and compare the values at `x w`.

Conclude with `pInf_algebraMap x w`. Rewrite using `[this]`. Conclude with `denseRange_embeddings'`. Take `⟨x, u, hu, hxu⟩` from `hd.exists_mem_open hU ⟨v.1, v, hv, rfl⟩`. Establish `hx : x ≠ 0`.

Introduce and unpack `rfl`. Simplify using `only [map_zero] at hxu`. Use `haveI : Nonempty (InfinitePlace E) := inferInstance`. Conclude with `u.ne_zero hxu`. Use `⟨Units.mk0 x hx, ?_⟩` and prove the remaining obligations.

Use `hu using 1` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using `[hxu]`.
-/
theorem exists_unit_mem_open :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty →
      ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  intro E _ _ _ V hV ⟨v, hv⟩
  have hU : IsOpen (Units.val '' V) := Units.isOpenEmbedding_val.isOpenMap V hV
  have hd : DenseRange fun x : E => pInf E (algebraMap E (Ad E) x) := by
    have : (fun x : E => pInf E (algebraMap E (Ad E) x)) = fun (x : E) (w : InfinitePlace E) => w.embedding x := by
      funext x w; exact pInf_algebraMap x w
    rw [this]; exact denseRange_embeddings'
  obtain ⟨x, u, hu, hxu⟩ := hd.exists_mem_open hU ⟨v.1, v, hv, rfl⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hxu
    haveI : Nonempty (InfinitePlace E) := inferInstance
    exact u.ne_zero hxu
  refine ⟨Units.mk0 x hx, ?_⟩
  convert hu using 1
  ext
  simp [hxu]

end GlobalTheory.UnitsDense
