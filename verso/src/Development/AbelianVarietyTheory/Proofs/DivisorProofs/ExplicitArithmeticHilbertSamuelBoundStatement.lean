import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBound
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSShortTop.geoBound_of_abstract` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExplicitArithmeticHilbertSamuelBound.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound : Quoted → BertiniNF → HeightTie → SlopeBound → GeoBound := by
  first | exact @GlobalTheory.HSShortTop.geoBound_of_abstract | exact GlobalTheory.HSShortTop.geoBound_of_abstract | (intros; apply GlobalTheory.HSShortTop.geoBound_of_abstract <;> assumption)
