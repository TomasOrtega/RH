import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStep
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.quasiLog_approx_step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuasiLogarithmSuccessiveApproximationStep.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.quasiLogarithm_successive_approximation_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.Katz.quasiLog_approx_step | exact GlobalTheory.Katz.quasiLog_approx_step | (intros; apply GlobalTheory.Katz.quasiLog_approx_step <;> assumption)
