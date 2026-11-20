import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrame
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FExistsHolomorphicNormalFrame.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.log_sine_mobius_transform : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | exact GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame <;> assumption)
