import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply `GlobalTheory.unifBaseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FUniformisationBaseChange.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.uniformisation_baseChange : PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → UnifBaseChangeSt := by
  first | exact @GlobalTheory.unifBaseChange | exact GlobalTheory.unifBaseChange | (intros; apply GlobalTheory.unifBaseChange <;> assumption)
