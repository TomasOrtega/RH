import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.chart_square_presents` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChartSquareCoordinatesPresentLevels.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.chart_square_coordinates_present_levels : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n, (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  first | exact @GlobalTheory.chart_square_presents | exact GlobalTheory.chart_square_presents | (intros; apply GlobalTheory.chart_square_presents <;> assumption)
