import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRiemannianHaarGaugeExistsPosUnique.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.riemannianHaarGauge_exists_pos_unique : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c := by
  first | exact @GlobalTheory.GaugeConst.gauge_exists_pos_unique | exact GlobalTheory.GaugeConst.gauge_exists_pos_unique | (intros; apply GlobalTheory.GaugeConst.gauge_exists_pos_unique <;> assumption)
