import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwV.isPtAd_mul_lev` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FChartBasePointRightTranslateByChartLevel.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  first | exact @GlobalTheory.TwV.isPtAd_mul_lev | exact GlobalTheory.TwV.isPtAd_mul_lev | (intros; apply GlobalTheory.TwV.isPtAd_mul_lev <;> assumption)
