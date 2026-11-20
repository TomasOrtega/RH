import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmoothStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChartStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBoundedPshCorrectionLocallySmooth.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
