import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeIndexImpliesHeightBound
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
Apply `GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FHodgeIndexImpliesHeightBound.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.hodge_index_implies_height_bound : MoriwakiHSStatement → ArithmeticHilbertSamuelUpperBound := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki | exact GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.smallCountUpper_of_moriwaki <;> assumption)
