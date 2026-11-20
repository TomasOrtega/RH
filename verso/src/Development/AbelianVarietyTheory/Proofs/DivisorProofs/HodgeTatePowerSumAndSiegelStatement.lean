import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePowerSumAndSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeTatePowerSumAndSiegel.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.hodge_tate_power_sum_and_siegel : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → OnObj fun _ O _ _ _ _ => PrimeLocalSplitCondition O.Y ∧ SiegRead O.Y := by
  first | exact @GlobalTheory.WholeHT.hodge_tate_power_sum_siegel_read | exact GlobalTheory.WholeHT.hodge_tate_power_sum_siegel_read | (intros; apply GlobalTheory.WholeHT.hodge_tate_power_sum_siegel_read <;> assumption)
