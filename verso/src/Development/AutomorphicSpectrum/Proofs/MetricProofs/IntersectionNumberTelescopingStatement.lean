import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescoping
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FIntersectionNumberTelescoping.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.intersection_number_telescoping : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) → IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 → I P (n + 1) (fun j => if (j : ℕ) < k then a else A') - I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') = -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope <;> assumption)
