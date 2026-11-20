import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderAction
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHodgeLatticeStableUnderAction.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.hodge_lattice_stable_under_action : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable <;> assumption)
