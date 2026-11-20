import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeries
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FTorsionCoordinatesEqDegenerationSeries.lean&line=459#L459)
-/
theorem _root_.GlobalTheory.T.torsionCoordinates_eq_degenerationSeries : HV → BrGtSt → BrFamSt → EVSt := by
  first | exact @GlobalTheory.Ex.CoordSeries.coord_eq_series | exact GlobalTheory.Ex.CoordSeries.coord_eq_series | (intros; apply GlobalTheory.Ex.CoordSeries.coord_eq_series <;> assumption)
