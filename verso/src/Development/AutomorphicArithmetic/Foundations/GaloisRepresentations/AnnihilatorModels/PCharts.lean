import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `l Y hY J _ T y`. Use `haveI : ∀ j, IsFinite (T j).p := fun j => (T j).fin`. Set `S : Set Y` to `{y} ∪ ⋃ j, (T j).r '' ((T j).p ⁻¹' {y})`. Establish `hS : S.Finite` using `(Set.finite_singleton y).union (Set.finite_iUnion fun j => ((T j).p.finite_preimage_singleton y).image _)`. Take `⟨V, hV, hSV⟩` from `hY hS.toFinset`.

Establish `hSV' : ∀ x ∈ S, x ∈ V` using `fun x hx => hSV x (hS.mem_toFinset.mpr hx)`. Establish `hclosed : IsClosed (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)` using `isClosed_iUnion_of_finite fun j => (T j).p.isClosedMap _ ((T j).r ⁻¹ᵁ V).isOpen.isClosed_compl`. Set `O : Y.Opens` to `⟨(⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ, hclosed.isOpen_compl⟩`. Establish `hyO : y ∈ O` using `by show y ∈ (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ`. Introduce and unpack `hy`.

Take `⟨j, z, hz, hzy⟩` from `Set.mem_iUnion.mp hy`. Apply `hz` to reduce the goal to its premises. Use `show (T j).r z ∈ V`. Conclude with `hSV' _ (Or.inr (Set.mem_iUnion.mpr ⟨j, z, hzy, rfl⟩))`. Take `⟨U, hU, hyU, hUO⟩` from `exists_isAffineOpen_mem_and_subset hyO`.

Use `⟨U, V, hU, hV, hyU, fun j z hz => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `hz' : (T j).p z ∈ (O : Set Y)` using `hUO hz`. Conclude with `hz' (Set.mem_iUnion.mpr ⟨j, z, h, rfl⟩)`.
-/
theorem UpperTheory.Gal.crystallineComparison.charts_of :
    ChartsExist := by
  intro l Y hY J _ T y
  haveI : ∀ j, IsFinite (T j).p := fun j => (T j).fin
  let S : Set Y := {y} ∪ ⋃ j, (T j).r '' ((T j).p ⁻¹' {y})
  have hS : S.Finite := (Set.finite_singleton y).union
    (Set.finite_iUnion fun j => ((T j).p.finite_preimage_singleton y).image _)
  obtain ⟨V, hV, hSV⟩ := hY hS.toFinset
  have hSV' : ∀ x ∈ S, x ∈ V := fun x hx => hSV x (hS.mem_toFinset.mpr hx)
  have hclosed : IsClosed (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ) :=
    isClosed_iUnion_of_finite fun j => (T j).p.isClosedMap _ ((T j).r ⁻¹ᵁ V).isOpen.isClosed_compl
  let O : Y.Opens := ⟨(⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hyO : y ∈ O := by
    show y ∈ (⋃ j, (T j).p '' ((T j).r ⁻¹ᵁ V : Set _)ᶜ)ᶜ
    rintro hy
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hy
    apply hz
    show (T j).r z ∈ V
    exact hSV' _ (Or.inr (Set.mem_iUnion.mpr ⟨j, z, hzy, rfl⟩))
  obtain ⟨U, hU, hyU, hUO⟩ := exists_isAffineOpen_mem_and_subset hyO
  refine ⟨U, V, hU, hV, hyU, fun j z hz => ?_⟩
  by_contra h
  have hz' : (T j).p z ∈ (O : Set Y) := hUO hz
  exact hz' (Set.mem_iUnion.mpr ⟨j, z, h, rfl⟩)
