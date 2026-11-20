import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.IndChar

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isChar_iff_coord {G : Type} [Group G] (χ : G → ℂ) :
    GlobalTheory.GLq.IsChar χ ↔ GlobalTheory.BI.IsChar ℂ ℂ χ := by
  constructor
  · rintro ⟨V, hV⟩

    let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
    refine ⟨Module.finrank ℂ V, GlobalTheory.BI.transportRep V.ρ e, fun g => ?_⟩
    rw [GlobalTheory.BI.character_transportRep, ← hV g]
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨FDRep.of ρ, fun g => ?_⟩
    rw [hρ g]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isChar_induced : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ), IsChar φ → IsChar (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G, if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) := by
  intro G _ _ H φ hφ

  have hind : GlobalTheory.BI.IsChar ℂ ℂ (GlobalTheory.BI.ind H φ) :=
    GlobalTheory.BI.isChar_ind ℂ ℂ G H φ ((isChar_iff_coord φ).mp hφ)
  have heq : (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G,
      if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) = GlobalTheory.BI.ind H φ := by
    funext x
    unfold GlobalTheory.BI.ind
    rw [finsum_eq_sum_of_fintype]
    congr 1
  rw [heq]
  exact (isChar_iff_coord _).mpr hind

end GlobalTheory.GLm.IndChar
