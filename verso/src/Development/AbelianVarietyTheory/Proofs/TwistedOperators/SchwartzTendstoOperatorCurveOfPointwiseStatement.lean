import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSchwartzTendstoOperatorCurveOfPointwise.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  first | exact @GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | exact GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | (intros; apply GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise <;> assumption)
