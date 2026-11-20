import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExtendToFractionField
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExtendToFractionField.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.extend_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay | exact GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay | (intros; apply GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay <;> assumption)
