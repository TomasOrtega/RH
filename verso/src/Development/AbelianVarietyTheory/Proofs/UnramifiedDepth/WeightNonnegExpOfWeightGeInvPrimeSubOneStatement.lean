import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightNonnegExpOfWeightGeInvPrimeSubOne
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExpWeight.weight_exp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FWeightNonnegExpOfWeightGeInvPrimeSubOne.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  first | exact @GlobalTheory.ExpWeight.weight_exp | exact GlobalTheory.ExpWeight.weight_exp | (intros; apply GlobalTheory.ExpWeight.weight_exp <;> assumption)
