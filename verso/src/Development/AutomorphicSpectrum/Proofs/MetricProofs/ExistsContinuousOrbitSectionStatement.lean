import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FExistsContinuousOrbitSection.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.exists_continuous_orbit_section : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X → ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts P) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts <;> assumption)
