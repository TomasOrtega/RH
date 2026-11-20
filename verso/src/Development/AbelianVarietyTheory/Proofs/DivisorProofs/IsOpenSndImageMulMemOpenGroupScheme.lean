import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

/- English proof (translation)
Introduce `S G _ hG U`. Establish `hs : Smooth (pullback.snd G.hom G.hom)` using `inferInstance`. Establish `ho : UniversallyOpen (pullback.snd G.hom G.hom)` using `UniversallyOpen.of_flat _`. Establish `hmap : IsOpenMap (snd G G).left` using `(pullback.snd G.hom G.hom).isOpenMap`. Establish `hW : IsOpen ((fst G G).left ⁻¹' (U : Set G.left) ∩ (μ[G]).left ⁻¹' (U : Set G.left))` using `((U.isOpen.preimage (fst G G).left.continuous)).inter (U.isOpen.preimage (μ[G]).left.continuous)`.

Use `hmap _ hW using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, h1, h2, h3⟩`.

Conclude with `⟨w, ⟨h1, h2⟩, h3⟩`. Introduce and unpack `⟨w, ⟨h1, h2⟩, h3⟩`. Conclude with `⟨w, h1, h2, h3⟩`.
-/
theorem isOpen_snd_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens,
    IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hG U
  have hs : Smooth (pullback.snd G.hom G.hom) := inferInstance
  have ho : UniversallyOpen (pullback.snd G.hom G.hom) := UniversallyOpen.of_flat _
  have hmap : IsOpenMap (snd G G).left := (pullback.snd G.hom G.hom).isOpenMap
  have hW : IsOpen ((fst G G).left ⁻¹' (U : Set G.left) ∩ (μ[G]).left ⁻¹' (U : Set G.left)) :=
    ((U.isOpen.preimage (fst G G).left.continuous)).inter (U.isOpen.preimage (μ[G]).left.continuous)
  convert hmap _ hW using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨w, h1, h2, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3⟩
  · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h1, h2, h3⟩

end GlobalTheory.IdCompOpen
