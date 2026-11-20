import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.DLocBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.Xgf.exists_local_basis'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FSesquilinearFractions%2FDLocBasis.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @PositivityTheory.Xgf.exists_local_basis' | exact PositivityTheory.Xgf.exists_local_basis'
