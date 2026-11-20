import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
/- English proof (citation)
Apply `GlobalTheory.splitTorus_to_abelian_const` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FSplitTorusToAbelianVarietyConst.lean&line=478#L478)
-/
theorem _root_.GlobalTheory.T.splitTorus_to_abelianVariety_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus (Sp K) X ⟶ B, ∃ b : 𝟙_ (Over (Sp K)) ⟶ B, f = toUnit _ ≫ b := by
  first | exact @GlobalTheory.splitTorus_to_abelian_const | exact GlobalTheory.splitTorus_to_abelian_const | (intros; apply GlobalTheory.splitTorus_to_abelian_const <;> assumption)
