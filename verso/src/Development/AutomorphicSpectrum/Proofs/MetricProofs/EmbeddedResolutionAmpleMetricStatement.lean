import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FEmbeddedResolutionAmpleMetric.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.embedded_resolution_ample_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | exact GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded <;> assumption)
