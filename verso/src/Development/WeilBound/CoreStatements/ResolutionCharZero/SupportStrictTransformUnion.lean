import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open FunctorialResolution

def GTransform : Prop :=
  ∀ (X X₁ : Scheme.{0}) (π : X₁ ⟶ X) (Z D : X.IdealSheafData), IsLocallyNoetherian X → IsLocallyNoetherian X₁ →
    IsBlowup π Z →
    ((strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) =
      π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransform_eq_blowup {X X₁ : Scheme.{0}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransform π Z D = Blowup.strictTransform π Z D := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails.

Prove the second alternative. Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
theorem support_strictTransform_union {X X₁ : Scheme.{0}} [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    ((strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) =
      π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X) := by
  rw [strictTransform_eq_blowup]
  apply Set.Subset.antisymm
  · refine Set.union_subset_union_left _ ?_
    exact EmbeddedResolution.support_strictTransform_subset_preimage π Z D
  · rintro x (hx | hx)
    · by_cases hz : π.base x ∈ (Z.support : Set X)
      · exact Or.inr hz
      · exact Or.inl ((EmbeddedResolution.mem_support_strictTransform_iff_of_notMem_support π Z D x hz).2 hx)
    · exact Or.inr hx

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem gTransform : GTransform := fun _ _ π Z D _ _ _ => support_strictTransform_union π Z D

end PositivityTheory.ResPlug.WeightsCompactStabilizer
