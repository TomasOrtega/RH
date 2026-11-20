import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResolutionGenericFibre
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsResolutionGenericFibre.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_resolution_generic_fibre : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → IsLocallyNoetherian (pullback Y.s (spMap β)) ∧ ∃ (X' : Scheme.{0}) (f : X' ⟶ pullback Y.s (spMap β)) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c), IsIso jW ∧ jW ≫ Y.jQ = W'.ι ≫ f ∧ IsProper f ∧ IsProper (f ≫ pullback.snd Y.s (spMap β)) ∧ SmoothOfRelativeDimension d (f ≫ pullback.snd Y.s (spMap β)) ∧ Geo.ResK.HasSncCoords (f ≫ pullback.snd Y.s (spMap β)) d (W' : Set X')ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre <;> assumption)
