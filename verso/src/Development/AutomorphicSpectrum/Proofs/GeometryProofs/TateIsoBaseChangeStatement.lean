import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoBaseChange
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
Apply `GlobalTheory.CompanionTheory.Relay.tate_iso_base_change` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTateIsoBaseChange.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.tate_iso_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (i : k →+* k') (x : Sp k ⟶ X), IsProper (pullback.snd t.G.hom x) → ∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t (spMap i ≫ x), ∀ n, 0 < n → (I'.ζ n : k') = i (I.ζ n) ∧ ∀ a, (I'.ev n a).left = spMap i ≫ (I.ev n a).left := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tate_iso_base_change | exact GlobalTheory.CompanionTheory.Relay.tate_iso_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.tate_iso_base_change <;> assumption)
