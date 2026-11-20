import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.newton_powerSeries_target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNewtonPowerSeriesSurjectiveLinearizationSolution.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.newton_powerSeries_surjective_linearization_solution : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  first | exact @GlobalTheory.newton_powerSeries_target | exact GlobalTheory.newton_powerSeries_target | (intros; apply GlobalTheory.newton_powerSeries_target <;> assumption)
