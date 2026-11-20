import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisati
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.familyUnif_of_thetaUnif` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FFamilyUniformisationOfAbelianVarietyUniformisati.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation : ThetaUnifAV → Out.Laws → N1c := by
  first | exact @GlobalTheory.familyUnif_of_thetaUnif | exact GlobalTheory.familyUnif_of_thetaUnif | (intros; apply GlobalTheory.familyUnif_of_thetaUnif <;> assumption)
