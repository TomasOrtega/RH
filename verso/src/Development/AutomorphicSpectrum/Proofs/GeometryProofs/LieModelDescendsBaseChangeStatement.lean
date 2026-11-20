import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelDescendsBaseChange.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.lie_model_descends_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E'), ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'), IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange | exact GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange <;> assumption)
