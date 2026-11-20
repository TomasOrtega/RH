import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem
import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.pushDown` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FPushDownOfArithIntersectionSystem.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.push_down_of_arith_intersection_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pushDown | exact GlobalTheory.CompanionTheory.Ar.Giv.pushDown | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pushDown <;> assumption)
