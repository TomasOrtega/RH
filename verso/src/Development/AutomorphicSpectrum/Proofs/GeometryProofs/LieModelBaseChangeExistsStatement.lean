import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeExists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.LieBc.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelBaseChangeExists.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.lie_model_base_change_exists : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (V : Type) [AddCommGroup V] [Module L V] (MV : LieModel G (𝟙 (Sp L)) V), ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module L' V') (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ (c : L) x, j (c • x) = e c • j x) ∧ Function.Injective j ∧ (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) ∧ Submodule.span L' (Set.range j) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieBc.main | exact GlobalTheory.CompanionTheory.Ar.LieBc.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieBc.main <;> assumption)
