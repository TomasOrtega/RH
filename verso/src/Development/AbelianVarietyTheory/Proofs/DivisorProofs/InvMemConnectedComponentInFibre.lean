import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Simplify using `only [Set.mem_setOf_eq] at hy ⊢`. Establish `hw : ∀ z : G.left, G.hom ((ι[G]).left z) = G.hom z`. Introduce `z`. Establish `h` using `Over.w (ι[G])`. Rewrite using `[← Scheme.Hom.comp_apply, h]`.

Establish `hη : ∀ s : S, (ι[G]).left ((η[G]).left s) = (η[G]).left s`. Introduce `s`. Establish `h : (η[G] ≫ ι[G]).left = (η[G]).left` using `by rw [GrpObj.one_inv]`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, h]`. Rewrite using `[hw]`.

Use `set F := G.hom ⁻¹' {G.hom y}`. Use `set e := (η[G]).left (G.hom y)`. Establish `heF : e ∈ F` using `(connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩)`. Establish `hsub : (ι[G]).left '' connectedComponentIn F e ⊆ connectedComponentIn F e`. Use `(isPreconnected_connectedComponentIn.image _ (ι[G]).left.continuous.continuousOn).subset_connectedComponentIn ⟨e, mem_connectedComponentIn heF, hη _⟩ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hzF : z ∈ F` using `connectedComponentIn_subset _ _ hz`. Simplify using `only [F, Set.mem_preimage, Set.mem_singleton_iff] at hzF ⊢`. Rewrite using `[hw, hzF]`. Conclude with `hsub ⟨y, hy, rfl⟩`.
-/
theorem inv_mem_connectedComponentIn_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left)
    (hy : y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hw : ∀ z : G.left, G.hom ((ι[G]).left z) = G.hom z := by
    intro z
    have h := Over.w (ι[G])
    rw [← Scheme.Hom.comp_apply, h]
  have hη : ∀ s : S, (ι[G]).left ((η[G]).left s) = (η[G]).left s := by
    intro s
    have h : (η[G] ≫ ι[G]).left = (η[G]).left := by rw [GrpObj.one_inv]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rw [hw]
  set F := G.hom ⁻¹' {G.hom y}
  set e := (η[G]).left (G.hom y)
  have heF : e ∈ F := (connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩)
  have hsub : (ι[G]).left '' connectedComponentIn F e ⊆ connectedComponentIn F e := by
    refine (isPreconnected_connectedComponentIn.image _ (ι[G]).left.continuous.continuousOn).subset_connectedComponentIn
      ⟨e, mem_connectedComponentIn heF, hη _⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzF : z ∈ F := connectedComponentIn_subset _ _ hz
    simp only [F, Set.mem_preimage, Set.mem_singleton_iff] at hzF ⊢
    rw [hw, hzF]
  exact hsub ⟨y, hy, rfl⟩

end GlobalTheory
