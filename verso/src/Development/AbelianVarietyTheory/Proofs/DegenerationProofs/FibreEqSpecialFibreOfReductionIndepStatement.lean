import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FFibreEqSpecialFibreOfReductionIndep.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep : ∀ C : Core, C.Indep → C.Fib := by
  first | exact @GlobalTheory.ZJ.Core.fib_of_indep | exact GlobalTheory.ZJ.Core.fib_of_indep | (intros; apply GlobalTheory.ZJ.Core.fib_of_indep <;> assumption)
