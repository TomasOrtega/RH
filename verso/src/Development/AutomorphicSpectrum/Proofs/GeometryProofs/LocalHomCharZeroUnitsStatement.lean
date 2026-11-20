import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnits
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLocalHomCharZeroUnits.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.local_hom_char_zero_units : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | exact GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf | (intros; apply GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf <;> assumption)
