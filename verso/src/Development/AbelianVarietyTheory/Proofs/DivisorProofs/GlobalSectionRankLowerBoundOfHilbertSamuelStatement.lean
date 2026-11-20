import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuel
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGlobalSectionRankLowerBoundOfHilbertSamuel.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel : Quoted → RankLow := by
  first | exact @GlobalTheory.HSCore.RankBound.rankLow | exact GlobalTheory.HSCore.RankBound.rankLow | (intros; apply GlobalTheory.HSCore.RankBound.rankLow <;> assumption)
