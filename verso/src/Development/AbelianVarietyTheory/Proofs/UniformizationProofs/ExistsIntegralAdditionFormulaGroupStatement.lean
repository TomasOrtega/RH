import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UU.exists_addG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FExistsIntegralAdditionFormulaGroup.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_integral_addition_formula_group : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  first | exact @GlobalTheory.UU.exists_addG | exact GlobalTheory.UU.exists_addG | (intros; apply GlobalTheory.UU.exists_addG <;> assumption)
