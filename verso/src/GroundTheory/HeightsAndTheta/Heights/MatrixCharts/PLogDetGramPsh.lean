import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PshMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric Real MCPsh

noncomputable section

/- English proof (translation)
Introduce `N g rk S`. Establish `hYc : ContinuousOn (fun x => (S.τ x).map Complex.im) S.W` using `continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => Complex.continuous_im.comp_continuousOn (S.τ_analytic j k).continuousOn`. Establish `hFc : ContinuousOn S.f S.W` using `continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (S.f_analytic j k).continuousOn`. Establish `hc` using `hcont (Fin N → ℂ) S.W g rk (fun x => (S.τ x).map Complex.im) S.f hYc hFc S.im_posDef S.f_rank`. Use `⟨hc.upperSemicontinuousOn, ?_⟩` and prove the remaining obligations.

Introduce `z w hdisc`. Establish `hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z + ζ • w ∈ S.W` using `fun ζ hζ => hdisc ζ (by simpa using hζ)`. Establish `haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ` using `fun ζ => analyticAt_const.add (analyticAt_id.smul analyticAt_const)`. Establish `hτ : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.τ (z + ζ • w) j k) (closedBall 0 1)` using `fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.τ x j k) (f := fun ζ : ℂ => z + ζ • w) (S.τ_analytic j k _ (hline ζ hζ)) (haff ζ)`. Establish `hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.f (z + ζ • w) j k) (closedBall 0 1)` using `fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.f x j k) (f := fun ζ : ℂ => z + ζ • w) (S.f_analytic j k _ (hline ζ hζ)) (haff ζ)`.

Establish `hYd : ContinuousOn (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im) (closedBall 0 1)` using `continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => Complex.continuous_im.comp_continuousOn (hτ j k).continuousOn`. Establish `hmean : ∀ j k, circleAverage (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im j k) 0 1 = (S.τ (z + (0:ℂ) • w)).map Complex.im j k` using `fun j k => by`. Simplify `circleAverage_im_of_analytic (hτ j k)` using `only [map_apply]`. Take `⟨hint, hle⟩` from `hsub g rk (fun ζ => (S.τ (z + ζ • w)).map Complex.im) (fun ζ => S.f (z + ζ • w)) (fun ζ hζ => S.im_posDef _ (hline ζ hζ)) hYd hmean hf (fun ζ hζ => S.f_rank _ (hline ζ hζ))`. Use `⟨hint, ?_⟩` and prove the remaining obligations.

Establish `e : z + (0:ℂ) • w = z` using `by simp`. Simplify `hle` using `only [e]`.
-/
theorem LogDetGramPsh.proof (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) : LogDetGramPsh.Statement := by
  intro N g rk S
  have hYc : ContinuousOn (fun x => (S.τ x).map Complex.im) S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (S.τ_analytic j k).continuousOn
  have hFc : ContinuousOn S.f S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (S.f_analytic j k).continuousOn
  have hc := hcont (Fin N → ℂ) S.W g rk (fun x => (S.τ x).map Complex.im) S.f hYc hFc
    S.im_posDef S.f_rank
  refine ⟨hc.upperSemicontinuousOn, ?_⟩
  intro z w hdisc
  have hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z + ζ • w ∈ S.W := fun ζ hζ =>
    hdisc ζ (by simpa using hζ)
  have haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hτ : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.τ (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.τ x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.τ_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.f (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.f x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.f_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hYd : ContinuousOn (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im) (closedBall 0 1) :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (hτ j k).continuousOn
  have hmean : ∀ j k, circleAverage (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im j k) 0 1 =
      (S.τ (z + (0:ℂ) • w)).map Complex.im j k := fun j k => by
    simpa only [map_apply] using circleAverage_im_of_analytic (hτ j k)
  obtain ⟨hint, hle⟩ := hsub g rk (fun ζ => (S.τ (z + ζ • w)).map Complex.im)
    (fun ζ => S.f (z + ζ • w)) (fun ζ hζ => S.im_posDef _ (hline ζ hζ)) hYd hmean hf
    (fun ζ hζ => S.f_rank _ (hline ζ hζ))
  refine ⟨hint, ?_⟩
  have e : z + (0:ℂ) • w = z := by simp
  simpa only [e] using hle

end

end GroundTheory.Heights₂.Heights
