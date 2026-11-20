import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FAgreementPositive.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.agreement_positive : AgreementPos := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.agreementPos | exact GlobalTheory.CompanionTheory.Ar.PB.agreementPos | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.agreementPos <;> assumption)
