import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivity
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBigLineImpliesHeightPositivity.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.big_line_implies_height_positivity : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | exact GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.selfIntersection_le_volNm_of_moriwakiBig <;> assumption)
