import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHessCCompPluri
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm Filter Topology

noncomputable section

/- English proof (translation)
Establish `hL2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 L w` using `hL.eventually (by simp)`. Establish `hF2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 F (L w)` using `hL.continuousAt.tendsto.eventually (hF.eventually (by simp))`. Establish `heq : fderiv ℝ (fun w => F (L w)) =ᶠ[𝓝 z] fun w => deriv F (L w) • fderiv ℝ L w` using `by filter_upwards [hL2, hF2] with w hw hFw`. Conclude with `((hFw.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt w (hw.differentiableAt (by norm_num)).hasFDerivAt).fderiv`. Establish `hdF : DifferentiableAt ℝ (deriv F) (L z)`.

Establish `h1` using `(hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Conclude with `h1.clm_apply (differentiableAt_const (1 : ℝ))`. Establish `hdL : DifferentiableAt ℝ (fderiv ℝ L) z` using `(hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hc : HasFDerivAt (fun w => deriv F (L w)) (deriv (deriv F) (L z) • fderiv ℝ L z) z` using `hdF.hasDerivAt.comp_hasFDerivAt z (hL.differentiableAt (by norm_num)).hasFDerivAt`. Establish `hs : HasFDerivAt (fun w => deriv F (L w) • fderiv ℝ L w) (deriv F (L z) • fderiv ℝ (fderiv ℝ L) z + (deriv (deriv F) (L z) • fderiv ℝ L z).smulRight (fderiv ℝ L z)) z` using `hc.smul hdL.hasFDerivAt`.

Rewrite using `[heq.fderiv_eq, hs.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HessCCompPluri.fderiv_fderiv_comp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ} {L : E → ℝ} {z : E} (hF : ContDiffAt ℝ 2 F (L z)) (hL : ContDiffAt ℝ 2 L z)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w => F (L w))) z v u =
      deriv (deriv F) (L z) * (fderiv ℝ L z v * fderiv ℝ L z u) +
        deriv F (L z) * fderiv ℝ (fderiv ℝ L) z v u := by
  have hL2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 L w := hL.eventually (by simp)
  have hF2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 F (L w) :=
    hL.continuousAt.tendsto.eventually (hF.eventually (by simp))
  have heq : fderiv ℝ (fun w => F (L w)) =ᶠ[𝓝 z] fun w => deriv F (L w) • fderiv ℝ L w := by
    filter_upwards [hL2, hF2] with w hw hFw
    exact ((hFw.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt w
      (hw.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdF : DifferentiableAt ℝ (deriv F) (L z) := by
    have h1 := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact h1.clm_apply (differentiableAt_const (1 : ℝ))
  have hdL : DifferentiableAt ℝ (fderiv ℝ L) z :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun w => deriv F (L w)) (deriv (deriv F) (L z) • fderiv ℝ L z) z :=
    hdF.hasDerivAt.comp_hasFDerivAt z (hL.differentiableAt (by norm_num)).hasFDerivAt
  have hs : HasFDerivAt (fun w => deriv F (L w) • fderiv ℝ L w)
      (deriv F (L z) • fderiv ℝ (fderiv ℝ L) z +
        (deriv (deriv F) (L z) • fderiv ℝ L z).smulRight (fderiv ℝ L z)) z :=
    hc.smul hdL.hasFDerivAt
  rw [heq.fderiv_eq, hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `D F L z hF hL h0`. Establish `hQ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 / 2) (L z)` using `((contDiff_id.pow 2).div_const 2).contDiffAt`. Establish `hd1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t`. Use function extensionality and compare the values at `t`. Rewrite using `[((hasDerivAt_pow 2 t).div_const 2).deriv]`.

Evaluate the numerical expressions. Establish `key` using `HessCCompPluri.fderiv_fderiv_comp_apply hF hL`. Establish `keyQ` using `HessCCompPluri.fderiv_fderiv_comp_apply hQ hL`. Simplify using `only [hd1, deriv_id'', one_mul] at keyQ`. Use extensionality with `i j`.

Establish `hij` using `congrFun (congrFun h0 i) j`. Simplify using `only [hessC, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢`. Simplify using `only [key, keyQ]`. Move the coercions through the operations in `at hij ⊢`. Take the linear combination `(((deriv F (L z) : ℝ) : ℂ) - ((deriv (deriv F) (L z) : ℝ) : ℂ) * ((L z : ℝ) : ℂ)) * hij`.
-/
theorem HessCCompPluri.proof : HessCCompPluri.Statement := by
  intro D F L z hF hL h0
  have hQ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 / 2) (L z) :=
    ((contDiff_id.pow 2).div_const 2).contDiffAt
  have hd1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := by
    funext t
    rw [((hasDerivAt_pow 2 t).div_const 2).deriv]
    norm_num
  have key := HessCCompPluri.fderiv_fderiv_comp_apply hF hL
  have keyQ := HessCCompPluri.fderiv_fderiv_comp_apply hQ hL
  simp only [hd1, deriv_id'', one_mul] at keyQ
  ext i j
  have hij := congrFun (congrFun h0 i) j
  simp only [hessC, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  simp only [key, keyQ]
  push_cast at hij ⊢
  linear_combination (((deriv F (L z) : ℝ) : ℂ) - ((deriv (deriv F) (L z) : ℝ) : ℂ) * ((L z : ℝ) : ℂ)) * hij

end

end GroundTheory.Heights₂.Heights
