import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
/- English proof (citation)
Apply `GlobalTheory.exists_psi_psiRel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FExistsPsiThetaExpansionPsiRelation.lean&line=203#L203)
-/
theorem _root_.GlobalTheory.T.exists_psi_thetaExpansionPsiRelation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  first | exact @GlobalTheory.exists_psi_psiRel | exact GlobalTheory.exists_psi_psiRel | (intros; apply GlobalTheory.exists_psi_psiRel <;> assumption)
