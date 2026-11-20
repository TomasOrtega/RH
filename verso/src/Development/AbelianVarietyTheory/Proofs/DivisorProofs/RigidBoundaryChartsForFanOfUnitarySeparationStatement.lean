import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanOfUnitarySeparation
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRigidBoundaryChartsForFanOfUnitarySeparation.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.rigidBoundaryChartsForFan_of_unitarySeparation : UStB → GlobalTheory.RigChart.RigidForFan := by
  first | exact @GlobalTheory.UChartJoin.rigidForFan_of_uStB | exact GlobalTheory.UChartJoin.rigidForFan_of_uStB | (intros; apply GlobalTheory.UChartJoin.rigidForFan_of_uStB <;> assumption)
