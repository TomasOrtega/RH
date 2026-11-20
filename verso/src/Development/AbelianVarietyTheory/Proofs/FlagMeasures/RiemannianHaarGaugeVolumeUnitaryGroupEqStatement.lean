import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRiemannianHaarGaugeVolumeUnitaryGroupEq.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c → c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  first | exact @GlobalTheory.UnitaryVolume.volume_unitary | exact GlobalTheory.UnitaryVolume.volume_unitary | (intros; apply GlobalTheory.UnitaryVolume.volume_unitary <;> assumption)
