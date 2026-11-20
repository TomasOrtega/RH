import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeriesOfIsNoetherianRing
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFormalGroupCharts%2FFlatMvPowerSeriesOfIsNoetherianRing.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by
  first | exact @GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | exact GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | (intros; apply GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing <;> assumption)
