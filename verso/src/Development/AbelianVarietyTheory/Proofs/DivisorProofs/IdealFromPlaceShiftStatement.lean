import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealFromPlaceShift
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealFromPlaceShift.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.ideal_from_place_shift : PlaceShiftSt → IdealSt := by
  first | exact @GlobalTheory.CMIdeal.idealSt_of_placeShiftSt | exact GlobalTheory.CMIdeal.idealSt_of_placeShiftSt | (intros; apply GlobalTheory.CMIdeal.idealSt_of_placeShiftSt <;> assumption)
