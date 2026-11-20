import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KFinAvg.peak_properties` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitaryRealTraceBumpPeakProperties.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.unitaryRealTraceBump_peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧ (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧ ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1, ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  first | exact @GlobalTheory.KFinAvg.peak_properties | exact GlobalTheory.KFinAvg.peak_properties | (intros; apply GlobalTheory.KFinAvg.peak_properties <;> assumption)
