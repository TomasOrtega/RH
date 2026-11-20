import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralMvPowerSeriesTwoEqZeroOfVanishOnSquares
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConvSer.eq_zero_of_ev_vanish` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FIntegralMvPowerSeriesTwoEqZeroOfVanishOnSquares.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.integralMvPowerSeries_two_eq_zero_of_vanish_on_squares : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  first | exact @GlobalTheory.ConvSer.eq_zero_of_ev_vanish | exact GlobalTheory.ConvSer.eq_zero_of_ev_vanish | (intros; apply GlobalTheory.ConvSer.eq_zero_of_ev_vanish <;> assumption)
