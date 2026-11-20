import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KFinAvg.peak_pow_polynomial` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitaryRealTraceBumpPowFiniteTranslationStablePo.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ), (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  first | exact @GlobalTheory.KFinAvg.peak_pow_polynomial | exact GlobalTheory.KFinAvg.peak_pow_polynomial | (intros; apply GlobalTheory.KFinAvg.peak_pow_polynomial <;> assumption)
