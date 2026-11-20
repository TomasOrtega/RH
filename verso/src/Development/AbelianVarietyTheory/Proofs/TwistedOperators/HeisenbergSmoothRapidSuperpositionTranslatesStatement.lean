import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergSmoothRapidSuperpositionTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealWeil.sm_superpos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHeisenbergSmoothRapidSuperpositionTranslates.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.heisenberg_smooth_rapid_superposition_translates : ∀ (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν : MeasureTheory.Measure Y) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → GlobalTheory.RealWeil.IsHeis (fun x y => om x y) ρ → ∀ (ι : Y →L[ℝ] V) (c : Y → ℂ), Continuous c → (∀ n : ℕ, MeasureTheory.Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) → ∀ f : B, GlobalTheory.RealWeil.Sm ρ f → GlobalTheory.RealWeil.Sm ρ (∫ y, c y • ρ (ι y) f ∂ν) := by
  first | exact @GlobalTheory.RealWeil.sm_superpos | exact GlobalTheory.RealWeil.sm_superpos | (intros; apply GlobalTheory.RealWeil.sm_superpos <;> assumption)
