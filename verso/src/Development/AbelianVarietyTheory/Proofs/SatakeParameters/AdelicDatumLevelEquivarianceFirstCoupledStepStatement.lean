import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAdelicDatumLevelEquivarianceFirstCoupledStep.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.AdLevCpl.levAt_coupled | exact GlobalTheory.AdLevCpl.levAt_coupled | (intros; apply GlobalTheory.AdLevCpl.levAt_coupled <;> assumption)
