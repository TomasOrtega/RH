import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullback
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTorsionAlongGroupPullback.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.torsion_along_group_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (x' : Sp R ⟶ S') (y : Sp R ⟶ S) (N : ℕ) (i₁ : Γ.G.left ⟶ G.left), IsGrpPullback G' G f φ → x' ≫ f = y → Γ.IsTorsionAlong G y N i₁ → ∃ i' : Γ.G.left ⟶ G'.left, i' ≫ φ = i₁ ∧ Γ.IsTorsionAlong G' x' N i' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong | exact GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong | (intros; apply GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong <;> assumption)
