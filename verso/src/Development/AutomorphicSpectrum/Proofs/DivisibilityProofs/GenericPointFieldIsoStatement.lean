import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericPointFieldIso
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FGenericPointFieldIso.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.generic_point_field_iso : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X), IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq | exact GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq <;> assumption)
