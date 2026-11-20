import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.unifUniq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FUniformisationDegenerationDataUnique.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.uniformisation_degenerationData_unique : GlobalFnsSt → SecBaseChangeSt → AmpleSt → UnifUniqSt := by
  first | exact @GlobalTheory.unifUniq | exact GlobalTheory.unifUniq | (intros; apply GlobalTheory.unifUniq <;> assumption)
