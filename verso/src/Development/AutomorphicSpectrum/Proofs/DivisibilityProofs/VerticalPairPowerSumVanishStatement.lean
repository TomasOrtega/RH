import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalPairPowerSumVanish
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FVerticalPairPowerSumVanish.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.vertical_pair_power_sum_vanish : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (σ : Type) [Fintype σ] (T : LocPair ι O σ), T.IsVert P ϖ → ∀ (r : ℕ) (e : Fin r → σ), PowerSumsVanish P d (T.x' ∘ e) → ∀ k m : ℕ, 1 ≤ k → k + m = d → ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, (∀ i, (Gs i).IsHomogeneous m) → T.val P (fun i => (∑ a, X (Sum.inr (e a)) ^ k) * Gs i) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.val_psum_mul_eq_zero <;> assumption)
