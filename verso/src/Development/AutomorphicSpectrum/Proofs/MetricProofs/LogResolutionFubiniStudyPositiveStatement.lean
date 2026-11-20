import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogResolutionFubiniStudyPositive.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.log_resolution_fubini_study_positive : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | exact GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential <;> assumption)
