import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
/- English proof (citation)
Apply `GlobalTheory.ZJ.Core.fibLaw_of_testCart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FFibreLawOfTestCartesian.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.fibreLaw_of_testCartesian : ∀ C : Core, C.TestCart → C.FibLaw := by
  first | exact @GlobalTheory.ZJ.Core.fibLaw_of_testCart | exact GlobalTheory.ZJ.Core.fibLaw_of_testCart | (intros; apply GlobalTheory.ZJ.Core.fibLaw_of_testCart <;> assumption)
