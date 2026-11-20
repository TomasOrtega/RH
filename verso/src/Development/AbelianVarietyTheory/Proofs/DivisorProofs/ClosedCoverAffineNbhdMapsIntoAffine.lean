import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/- English proof (translation)
Introduce `Y Y₁ Y₂ X j₁ j₂ _ _ a₁ a₂ hcov hagree y`. Establish `hinj₁` using `j₁.isClosedEmbedding.injective`. Establish `hinj₂` using `j₂.isClosedEmbedding.injective`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx₁, hx₂⟩ : ∃ x : X, (∀ w, j₁ w = y → a₁ w = x) ∧ (∀ w, j₂ w = y → a₂ w = x) := by`. Break down `hcov y with ⟨y₁, h₁⟩ | ⟨y₂, h₂⟩` into its components or cases.

Use `⟨a₁ y₁, fun w hw => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hinj₁ (hw.trans h₁.symm)]`. Conclude with `(hagree y₁ w (h₁.trans hw.symm)).symm`. Use `⟨a₂ y₂, fun w hw => hagree w y₂ (hw.trans h₂.symm), fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hinj₂ (hw.trans h₂.symm)]`.

Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Use `set C : Set Y := j₁.base '' ((a₁ ⁻¹ᵁ U : Set Y₁)ᶜ) ∪ j₂.base '' ((a₂ ⁻¹ᵁ U : Set Y₂)ᶜ) with hCdef`. Establish `hC : IsClosed C` using `(j₁.isClosedEmbedding.isClosedMap _ (a₁ ⁻¹ᵁ U).isOpen.isClosed_compl).union (j₂.isClosedEmbedding.isClosedMap _ (a₂ ⁻¹ᵁ U).isOpen.isClosed_compl)`. Establish `hyC : y ∉ C`. Introduce and unpack `(⟨w, hw, hwy⟩ | ⟨w, hw, hwy⟩)`.

Conclude with `hw (by simpa [hx₁ w hwy] using hxU)`. Conclude with `hw (by simpa [hx₂ w hwy] using hxU)`. Take `⟨W, hW, hyW, hWC⟩` from `exists_isAffineOpen_mem_and_subset (U := ⟨Cᶜ, hC.isOpen_compl⟩) (show y ∈ Cᶜ from hyC)`. Use `⟨W, ⟨U, hU⟩, hW, hyW, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Assume the negation of the conclusion as `hn`. Conclude with `hWC hw (Or.inl ⟨w, hn, rfl⟩)`. Introduce `w hw`. Assume the negation of the conclusion as `hn`. Conclude with `hWC hw (Or.inr ⟨w, hn, rfl⟩)`.
-/
theorem closedCover_affine_nbhd_maps_into_affine :
    ∀ (Y Y₁ Y₂ X : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) [IsClosedImmersion j₁]
      [IsClosedImmersion j₂] (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X),
      (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) →
      (∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂) →
      ∀ y : Y, ∃ (W : Y.Opens) (U : X.affineOpens), IsAffineOpen W ∧ y ∈ W ∧
        j₁ ⁻¹ᵁ W ≤ a₁ ⁻¹ᵁ U.1 ∧ j₂ ⁻¹ᵁ W ≤ a₂ ⁻¹ᵁ U.1 := by
  intro Y Y₁ Y₂ X j₁ j₂ _ _ a₁ a₂ hcov hagree y
  have hinj₁ := j₁.isClosedEmbedding.injective
  have hinj₂ := j₂.isClosedEmbedding.injective

  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : X, (∀ w, j₁ w = y → a₁ w = x) ∧ (∀ w, j₂ w = y → a₂ w = x) := by
    rcases hcov y with ⟨y₁, h₁⟩ | ⟨y₂, h₂⟩
    · refine ⟨a₁ y₁, fun w hw => ?_, fun w hw => ?_⟩
      · rw [hinj₁ (hw.trans h₁.symm)]
      · exact (hagree y₁ w (h₁.trans hw.symm)).symm
    · refine ⟨a₂ y₂, fun w hw => hagree w y₂ (hw.trans h₂.symm), fun w hw => ?_⟩
      rw [hinj₂ (hw.trans h₂.symm)]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  set C : Set Y := j₁.base '' ((a₁ ⁻¹ᵁ U : Set Y₁)ᶜ) ∪ j₂.base '' ((a₂ ⁻¹ᵁ U : Set Y₂)ᶜ) with hCdef
  have hC : IsClosed C :=
    (j₁.isClosedEmbedding.isClosedMap _ (a₁ ⁻¹ᵁ U).isOpen.isClosed_compl).union
      (j₂.isClosedEmbedding.isClosedMap _ (a₂ ⁻¹ᵁ U).isOpen.isClosed_compl)
  have hyC : y ∉ C := by
    rintro (⟨w, hw, hwy⟩ | ⟨w, hw, hwy⟩)
    · exact hw (by simpa [hx₁ w hwy] using hxU)
    · exact hw (by simpa [hx₂ w hwy] using hxU)
  obtain ⟨W, hW, hyW, hWC⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨Cᶜ, hC.isOpen_compl⟩) (show y ∈ Cᶜ from hyC)
  refine ⟨W, ⟨U, hU⟩, hW, hyW, ?_, ?_⟩
  · intro w hw
    by_contra hn
    exact hWC hw (Or.inl ⟨w, hn, rfl⟩)
  · intro w hw
    by_contra hn
    exact hWC hw (Or.inr ⟨w, hn, rfl⟩)

end GlobalTheory
