import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartFormalBiextensionBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.rawChart_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCuspFormEvaluations%2FRawChartFormalBiextensionBaseChange.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.rawChart_formalBiextension_baseChange : RawBCSt := by
  first | exact @GlobalTheory.rawChart_baseChange | exact GlobalTheory.rawChart_baseChange | (intros; apply GlobalTheory.rawChart_baseChange <;> assumption)
