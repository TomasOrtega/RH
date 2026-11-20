import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasis
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.exists_local_basis'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FExistsLocalBasis.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis' | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis' | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis' <;> assumption)
