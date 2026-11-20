import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.ThetaSeries.theta_const_eq_series` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FThetaConstantsEqDegenerationSeries.lean&line=354#L354)
-/
theorem _root_.GlobalTheory.T.theta_constants_eq_degeneration_series : HV → BrGtSt → BrFamSt → TXSt := by
  first | exact @GlobalTheory.Ex.ThetaSeries.theta_const_eq_series | exact GlobalTheory.Ex.ThetaSeries.theta_const_eq_series | (intros; apply GlobalTheory.Ex.ThetaSeries.theta_const_eq_series <;> assumption)
