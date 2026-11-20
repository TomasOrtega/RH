import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullLevelFiniteExtension
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsFullLevelFiniteExtension.lean&line=202#L202)
-/
theorem _root_.GlobalTheory.T.exists_full_level_finite_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (N : ℕ), 1 ≤ N → ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (z : Ωˣ) (ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G)), FiniteDimensional K Ω ∧ IsFullLevelAt D Y.t (spMap (algebraMap K Ω) ≫ y ≫ Y.j) N z ev := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite | exact GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.exists_fullLevel_finite <;> assumption)
