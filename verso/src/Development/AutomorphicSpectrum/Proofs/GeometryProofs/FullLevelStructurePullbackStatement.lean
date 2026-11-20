import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePullback
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
Apply `GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFullLevelStructurePullback.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.full_level_structure_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X'), ξ' ≫ f = spMap i ≫ ξ → ∀ (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ ev' : D.La → (Over.mk ξ' ⟶ t'.G), IsFullLevelAt D t' ξ' N (Units.map i.toMonoidHom z) ev' ∧ ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move <;> assumption)
