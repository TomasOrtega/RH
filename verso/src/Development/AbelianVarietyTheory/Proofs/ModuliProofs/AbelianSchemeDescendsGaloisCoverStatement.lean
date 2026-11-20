import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescendsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.abelianScheme_descends_galoisCover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FAbelianSchemeDescendsGaloisCover.lean&line=159#L159)
-/
theorem _root_.GlobalTheory.T.exists_abelianScheme_descent_of_galoisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover | exact GlobalTheory.abelianScheme_descends_galoisCover | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover <;> assumption)
