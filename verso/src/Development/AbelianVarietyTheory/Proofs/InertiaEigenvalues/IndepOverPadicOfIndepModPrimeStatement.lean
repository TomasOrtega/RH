import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOverPadicOfIndepModPrime
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIndepOverPadicOfIndepModPrime.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.indep_over_padic_of_indep_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  first | exact @GlobalTheory.indep_over_Ql_of_indep_mod_l | exact GlobalTheory.indep_over_Ql_of_indep_mod_l | (intros; apply GlobalTheory.indep_over_Ql_of_indep_mod_l <;> assumption)
