import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

/- English proof (translation)
Introduce `TT α c hTT hα hre R hR hR2`. Establish `hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ)`. Introduce `θ`. Establish `h1 : ‖circleMap 0 R θ‖ = R` using `by rw [norm_circleMap_zero, abs_of_pos hR]`. Rewrite using `[Complex.normSq_eq_norm_sq, h1]`.

Conclude with `hR2`. Establish `hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ))` using `hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt`. Establish `hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I`. Use function extensionality and compare the values at `θ`. Conclude with `deriv_circleMap 0 R θ`.

Establish `hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ))`. Establish `h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ)`. Rewrite using `[hd]`. Conclude with `(continuous_circleMap 0 R).mul continuous_const`. Conclude with `h2.smul hcα`.

Establish `key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c`. Introduce `θ`. Rewrite using `[deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]`. Rewrite using `[← hre (circleMap 0 R θ) (hpt θ)]`. Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `circleIntegral`. Rewrite using `[← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]`. Simplify using `only [key]`. Rewrite using `[intervalIntegral.integral_const, smul_eq_mul, sub_zero]`.
-/
theorem reference_annulus_holds : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
