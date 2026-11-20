import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSncResolutionRegularLocalRing.lean&line=399#L399)
-/
theorem _root_.GlobalTheory.T.snc_resolution_regular_local_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) ∧ ringKrullDim (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart <;> assumption)
