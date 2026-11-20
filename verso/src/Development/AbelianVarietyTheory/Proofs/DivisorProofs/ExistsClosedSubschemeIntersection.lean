import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `H Z₁ Z₂ i₁ i₂ h₁ h₂`. Use `⟨pullback i₁ i₂, pullback.snd i₁ i₂ ≫ i₂, inferInstance, ?_⟩` and prove the remaining obligations. Introduce `T h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`.

Use `⟨⟨z ≫ pullback.fst i₁ i₂, ?_⟩, ⟨z ≫ pullback.snd i₁ i₂, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition]`. Rewrite using `[Category.assoc]`. Introduce and unpack `⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩`. Conclude with `⟨pullback.lift z₁ z₂ (hz₁.trans hz₂.symm), by rw [← Category.assoc, pullback.lift_snd, hz₂]⟩`.
-/
theorem closedSubscheme_inter_exists : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H),
      IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H),
        (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  intro H Z₁ Z₂ i₁ i₂ h₁ h₂
  refine ⟨pullback i₁ i₂, pullback.snd i₁ i₂ ≫ i₂, inferInstance, ?_⟩
  intro T h
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ pullback.fst i₁ i₂, ?_⟩, ⟨z ≫ pullback.snd i₁ i₂, ?_⟩⟩
    · rw [Category.assoc, pullback.condition]
    · rw [Category.assoc]
  · rintro ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩
    exact ⟨pullback.lift z₁ z₂ (hz₁.trans hz₂.symm), by rw [← Category.assoc, pullback.lift_snd, hz₂]⟩

end GlobalTheory
