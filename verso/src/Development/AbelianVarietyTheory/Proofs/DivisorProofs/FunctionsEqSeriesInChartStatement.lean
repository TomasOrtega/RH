import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.Chart.functions_are_series` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFunctionsEqSeriesInChart.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.functions_eq_series_in_chart : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n f, G.res n (c.ev (n + 1) f) = c.ev n f) ∧ (∀ n s, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s) ∧ ∀ b : ∀ n, G.A n, (∀ n, G.res n (b (n + 1)) = b n) → ∃! f, ∀ n, c.ev n f = b n := by
  first | exact @GlobalTheory.Katz.Chart.functions_are_series | exact GlobalTheory.Katz.Chart.functions_are_series | (intros; apply GlobalTheory.Katz.Chart.functions_are_series <;> assumption)
