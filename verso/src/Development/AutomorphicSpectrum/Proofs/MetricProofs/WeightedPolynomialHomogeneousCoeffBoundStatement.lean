import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedPolynomialHomogeneousCoeffBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FWeightedPolynomialHomogeneousCoeffBound.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_holomorphic_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | exact GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame <;> assumption)
