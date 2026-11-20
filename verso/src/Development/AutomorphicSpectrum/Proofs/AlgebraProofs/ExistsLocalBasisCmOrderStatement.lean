import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisCmOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FExistsLocalBasisCmOrder.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order <;> assumption)
