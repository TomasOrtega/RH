import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSmoothCommGroupSchemeEqOfPowEqOfClosedPoint.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ S) (k : ℕ), IsUnit (k : A) →
    ∀ (x y : Over.mk s ⟶ G), x ^ k = y ^ k →
    ∀ (κ : Type) [Field κ] (c : A →+* κ), IsLocalHom c → spMap c ≫ x.left = spMap c ≫ y.left → x = y := by
  first | exact @GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint | exact GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint | (intros; apply GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint <;> assumption)
