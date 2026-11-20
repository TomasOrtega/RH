import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmDifferentFromIdeal.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.cm_different_from_ideal : IdealSt → GlobalTheory.FlatCore.CMDiffSt := by
  first | exact @GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt | exact GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt | (intros; apply GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt <;> assumption)
