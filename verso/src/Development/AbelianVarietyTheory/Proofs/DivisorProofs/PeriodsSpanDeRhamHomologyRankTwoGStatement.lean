import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoG
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodSpan.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodsSpanDeRhamHomologyRankTwoG.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.periods_span_deRhamHomology_rank_two_g : PSpan := by
  first | exact @GlobalTheory.PeriodSpan.main | exact GlobalTheory.PeriodSpan.main | (intros; apply GlobalTheory.PeriodSpan.main <;> assumption)
