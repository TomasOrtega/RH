import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FIsMonHomPointedSplitExtToAbelianVariety.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  first | exact @GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | exact GlobalTheory.ExtensionRigidity.isMonHom_of_pointed | (intros; apply GlobalTheory.ExtensionRigidity.isMonHom_of_pointed <;> assumption)
