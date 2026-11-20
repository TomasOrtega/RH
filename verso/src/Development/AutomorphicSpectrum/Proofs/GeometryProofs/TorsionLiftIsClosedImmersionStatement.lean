import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTorsionLiftIsClosedImmersion.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.torsion_lift_is_closed_immersion : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom] (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left) (h : Γ.IsTorsionAlong G x N i), IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift | exact GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift <;> assumption)
