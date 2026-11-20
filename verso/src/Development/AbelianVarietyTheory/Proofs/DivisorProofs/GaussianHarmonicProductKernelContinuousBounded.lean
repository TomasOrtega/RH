import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpace
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckeTheta.GaussBound

open GlobalTheory.HeckeTheta

/- English proof (translation)
Introduce `I _ n`. Use `⟨?_, ⟨Decay.gC n, fun w => ?_⟩⟩` and prove the remaining obligations. Unfold `gauss`. Use `continuous_finset_prod _ fun i _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun w : EuclideanSpace ℂ I => (WithLp.ofLp w) i` using `(continuous_apply i).comp (PiLp.continuous_ofLp 2 _)`.

Conclude with `((Decay.continuous_hmon _).comp hc).mul (by fun_prop)`. Establish `h` using `Decay.norm_gauss_le n (WithLp.ofLp w)`. Establish `e : ‖w‖ ^ 2 = ∑ i, ‖(WithLp.ofLp w) i‖ ^ 2` using `EuclideanSpace.norm_sq_eq w`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem gauss_cont_bound : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro I _ n
  refine ⟨?_, ⟨Decay.gC n, fun w => ?_⟩⟩
  · unfold gauss
    refine continuous_finset_prod _ fun i _ => ?_
    have hc : Continuous fun w : EuclideanSpace ℂ I => (WithLp.ofLp w) i :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    exact ((Decay.continuous_hmon _).comp hc).mul (by fun_prop)
  · have h := Decay.norm_gauss_le n (WithLp.ofLp w)
    have e : ‖w‖ ^ 2 = ∑ i, ‖(WithLp.ofLp w) i‖ ^ 2 := EuclideanSpace.norm_sq_eq w
    rw [e]; exact h

end GlobalTheory.HeckeTheta.GaussBound
