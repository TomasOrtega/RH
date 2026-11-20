import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
open MeasureTheory

namespace GlobalTheory

open LineDeriv

/- English proof (translation)
Set `L : V →L[ℝ] ℂ` to `Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))`. Establish `hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ))` using `L.hasTemperateGrowth`. Use `⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL, SchwartzMap.lineDerivOp_apply_eq_fderiv]`.

Simplify using `[GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dHeis_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))
  have hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ)) := L.hasTemperateGrowth
  refine ⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩
  intro x
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]
  ring

end GlobalTheory
