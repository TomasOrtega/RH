import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConst

/- English proof (translation)
The claim follows from `GlobalTheory.GaugeConst.exists_unique_isGauge`.
-/
theorem gauge_exists_pos_unique :
    ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c :=
  GlobalTheory.GaugeConst.exists_unique_isGauge

end GlobalTheory.GaugeConst
