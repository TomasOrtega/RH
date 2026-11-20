import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CM.PureDeg.degSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FCmEigenLineDegreeFormula.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.cmEigenLine_degreeFormula : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → DegSt := by
  first | exact @GlobalTheory.CM.PureDeg.degSt | exact GlobalTheory.CM.PureDeg.degSt | (intros; apply GlobalTheory.CM.PureDeg.degSt <;> assumption)
