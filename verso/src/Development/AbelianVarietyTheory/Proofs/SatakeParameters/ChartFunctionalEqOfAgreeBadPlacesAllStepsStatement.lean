import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwV.fnl_eq_of_away_cpl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FChartFunctionalEqOfAgreeBadPlacesAllSteps.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  first | exact @GlobalTheory.TwV.fnl_eq_of_away_cpl | exact GlobalTheory.TwV.fnl_eq_of_away_cpl | (intros; apply GlobalTheory.TwV.fnl_eq_of_away_cpl <;> assumption)
