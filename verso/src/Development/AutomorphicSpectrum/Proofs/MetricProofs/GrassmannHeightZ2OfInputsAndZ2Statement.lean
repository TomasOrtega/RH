import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2
import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGrassmannHeightZ2OfInputsAndZ2.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.grassmann_height_Z2_of_inputs_and_Z2 : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push | exact GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.grassmann_height_Z2_of_push <;> assumption)
