import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointLeftTranslateRationalUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwRat.ratPt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FChartPointLeftTranslateRationalUnitary.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  first | exact @GlobalTheory.TwRat.ratPt | exact GlobalTheory.TwRat.ratPt | (intros; apply GlobalTheory.TwRat.ratPt <;> assumption)
