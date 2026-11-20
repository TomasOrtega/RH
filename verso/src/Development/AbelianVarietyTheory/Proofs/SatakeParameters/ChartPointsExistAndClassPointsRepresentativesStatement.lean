import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentatives
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FChartPointsExistAndClassPointsRepresentatives.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.chartPoints_exist_and_classPoints_representatives : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  first | exact @GlobalTheory.TwV.ptEx_isPtAd | exact GlobalTheory.TwV.ptEx_isPtAd | (intros; apply GlobalTheory.TwV.ptEx_isPtAd <;> assumption)
