import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtension
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FEigenspaceFieldExtension.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.eigenspace_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | exact GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext <;> assumption)
