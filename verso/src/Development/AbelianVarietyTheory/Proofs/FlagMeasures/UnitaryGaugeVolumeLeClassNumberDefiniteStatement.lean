import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefiniteVolume.gaugeVol_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitaryGaugeVolumeLeClassNumberDefinite.lean&line=213#L213)
-/
theorem _root_.GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite : ∀ (I : AutInst) (r : ℕ), HasSig I r 0 → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (volU r ^ I.f) * ((defClassNum I.E r : ENat) : ENNReal) := by
  first | exact @GlobalTheory.DefiniteVolume.gaugeVol_le | exact GlobalTheory.DefiniteVolume.gaugeVol_le | (intros; apply GlobalTheory.DefiniteVolume.gaugeVol_le <;> assumption)
