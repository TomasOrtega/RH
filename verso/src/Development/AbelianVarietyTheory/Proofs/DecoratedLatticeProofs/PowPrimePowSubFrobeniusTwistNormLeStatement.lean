import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FPowPrimePowSubFrobeniusTwistNormLe.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.pow_frob_sub_le | exact GlobalTheory.Honda.pow_frob_sub_le | (intros; apply GlobalTheory.Honda.pow_frob_sub_le <;> assumption)
