import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatMvPowerSeries

open IsLocalRing TensorProduct

namespace GlobalTheory.FiniteHeight

/- English proof (translation)
The claim follows from `GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries`.
-/
theorem flat_mvPowerSeries_of_isNoetherianRing :
    ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type),
      Module.Flat T (MvPowerSeries σ T) :=
  GlobalTheory.PowerSeriesFlat.flat_mvPowerSeries

end GlobalTheory.FiniteHeight
