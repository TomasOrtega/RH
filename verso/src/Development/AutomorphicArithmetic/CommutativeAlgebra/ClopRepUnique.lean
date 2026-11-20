import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.preimage_whiskerRight_comp_over {S : Scheme.{0}} {A B C G : Over S} (f : A ⟶ B) (g : B ⟶ C)
    (W : (C ⊗ G).left.Opens) :
    ((f ≫ g) ▷ G).left ⁻¹ᵁ W = (f ▷ G).left ⁻¹ᵁ ((g ▷ G).left ⁻¹ᵁ W) := by
  simp

/- English proof (translation)
Introduce `S G Y Y' U U' hU hU'`. Take `⟨φ, hφ, -⟩` from `hU'.2 Y U hU.1`. Take `⟨ψ, hψ, -⟩` from `hU.2 Y' U' hU'.1`. Establish `hid : ∀ {Z : Over S} (W : (Z ⊗ G).left.Opens), ((𝟙 Z) ▷ G).left ⁻¹ᵁ W = W`. Introduce `Z W`.

Simplify using the standard rewrite rules. Establish `e1 : φ ≫ ψ = 𝟙 Y`. Take `⟨y, -, huniq⟩` from `hU.2 Y U hU.1`. Establish `a` using `huniq (φ ≫ ψ) (by show ((φ ≫ ψ) ▷ G).left ⁻¹ᵁ U = U`. Rewrite using `[UpperTheory.preimage_whiskerRight_comp_over, hψ, hφ])`.

Establish `b` using `huniq (𝟙 Y) (hid U)`. Rewrite using `[a, b]`. Establish `e2 : ψ ≫ φ = 𝟙 Y'`. Take `⟨y, -, huniq⟩` from `hU'.2 Y' U' hU'.1`. Establish `a` using `huniq (ψ ≫ φ) (by show ((ψ ≫ φ) ▷ G).left ⁻¹ᵁ U' = U'`.

Rewrite using `[UpperTheory.preimage_whiskerRight_comp_over, hφ, hψ])`. Establish `b` using `huniq (𝟙 Y') (hid U')`. Rewrite using `[a, b]`. Conclude with `⟨⟨φ, ψ, e1, e2⟩⟩`.
-/
theorem UpperTheory.clopRep_unique :
    ∀ {S : Scheme.{0}} (G Y Y' : Over S) (U : (Y ⊗ G).left.Opens) (U' : (Y' ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → UpperTheory.RepresentationRank.Rep G Y' U' → Nonempty (Y ≅ Y') := by
  intro S G Y Y' U U' hU hU'
  obtain ⟨φ, hφ, -⟩ := hU'.2 Y U hU.1
  obtain ⟨ψ, hψ, -⟩ := hU.2 Y' U' hU'.1
  have hid : ∀ {Z : Over S} (W : (Z ⊗ G).left.Opens), ((𝟙 Z) ▷ G).left ⁻¹ᵁ W = W := by
    intro Z W
    simp
  have e1 : φ ≫ ψ = 𝟙 Y := by
    obtain ⟨y, -, huniq⟩ := hU.2 Y U hU.1
    have a := huniq (φ ≫ ψ) (by
      show ((φ ≫ ψ) ▷ G).left ⁻¹ᵁ U = U
      rw [UpperTheory.preimage_whiskerRight_comp_over, hψ, hφ])
    have b := huniq (𝟙 Y) (hid U)
    rw [a, b]
  have e2 : ψ ≫ φ = 𝟙 Y' := by
    obtain ⟨y, -, huniq⟩ := hU'.2 Y' U' hU'.1
    have a := huniq (ψ ≫ φ) (by
      show ((ψ ≫ φ) ▷ G).left ⁻¹ᵁ U' = U'
      rw [UpperTheory.preimage_whiskerRight_comp_over, hφ, hψ])
    have b := huniq (𝟙 Y') (hid U')
    rw [a, b]
  exact ⟨⟨φ, ψ, e1, e2⟩⟩
