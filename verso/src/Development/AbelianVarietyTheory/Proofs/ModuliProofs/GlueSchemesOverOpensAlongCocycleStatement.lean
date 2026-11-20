import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CocycleGlue.glue_over_opens` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FGlueSchemesOverOpensAlongCocycle.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.glue_schemes_over_opens_along_cocycle : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  first | exact @GlobalTheory.CocycleGlue.glue_over_opens | exact GlobalTheory.CocycleGlue.glue_over_opens | (intros; apply GlobalTheory.CocycleGlue.glue_over_opens <;> assumption)
