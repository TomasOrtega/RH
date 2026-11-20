import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsLaplacianHoloComp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Filter Topology

/- English proof (translation)
Use `set A : ℂ → ℂ →L[ℝ] ℂ := fun s => ContinuousLinearMap.lsmul ℝ ℂ (deriv T s) with hAdef`. Establish `hTev : ∀ᶠ s in 𝓝 t, AnalyticAt ℂ T s` using `hT.eventually_analyticAt`. Establish `hφev : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 φ (T s)` using `hT.continuousAt.tendsto.eventually (hφ.eventually (by simp))`. Establish `hfd : fderiv ℝ (φ ∘ T) =ᶠ[𝓝 t] fun s => (fderiv ℝ φ (T s)).comp (A s)` using `by filter_upwards [hTev, hφev] with s hs hs'`. Establish `h1 : HasFDerivAt T ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T s)).restrictScalars ℝ) s` using `hs.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ`.

Establish `h2` using `(hs'.differentiableAt (by norm_num)).hasFDerivAt.comp s h1`. Rewrite using `[h2.fderiv]`. Use `congr 1`. Use extensionality with `w`. Simplify using `[hAdef, mul_comm]`.

Establish `hT1 : HasFDerivAt T ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T t)).restrictScalars ℝ) t` using `hT.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ`. Establish `hc : HasFDerivAt (fun s => fderiv ℝ φ (T s)) ((fderiv ℝ (fderiv ℝ φ) (T t)).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T t)).restrictScalars ℝ)) t`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ φ) (T t)` using `(hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Conclude with `hd.hasFDerivAt.comp t hT1`. Establish `hT2 : HasFDerivAt (deriv T) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv T) t)).restrictScalars ℝ) t` using `hT.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ`.

Establish `hA : HasFDerivAt A ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv T) t)).restrictScalars ℝ)) t` using `(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).hasFDerivAt.comp t hT2`. Establish `hG` using `hc.clm_comp hA`. Rewrite using `[hfd.fderiv_eq, hG.fderiv]`. Simplify using `[hAdef, mul_comm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_fderiv_comp_holo_apply (φ : ℂ → ℝ) (T : ℂ → ℂ) (t : ℂ)
    (hφ : ContDiffAt ℝ 2 φ (T t)) (hT : AnalyticAt ℂ T t) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ T)) t v v =
      fderiv ℝ (fderiv ℝ φ) (T t) (deriv T t * v) (deriv T t * v) +
        fderiv ℝ φ (T t) (deriv (deriv T) t * v * v) := by

  set A : ℂ → ℂ →L[ℝ] ℂ := fun s => ContinuousLinearMap.lsmul ℝ ℂ (deriv T s) with hAdef
  have hTev : ∀ᶠ s in 𝓝 t, AnalyticAt ℂ T s := hT.eventually_analyticAt
  have hφev : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 φ (T s) :=
    hT.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (φ ∘ T) =ᶠ[𝓝 t] fun s => (fderiv ℝ φ (T s)).comp (A s) := by
    filter_upwards [hTev, hφev] with s hs hs'
    have h1 : HasFDerivAt T
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T s)).restrictScalars ℝ) s :=
      hs.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
    have h2 := (hs'.differentiableAt (by norm_num)).hasFDerivAt.comp s h1
    rw [h2.fderiv]
    congr 1
    ext w
    simp [hAdef, mul_comm]

  have hT1 : HasFDerivAt T
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T t)).restrictScalars ℝ) t :=
    hT.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun s => fderiv ℝ φ (T s))
      ((fderiv ℝ (fderiv ℝ φ) (T t)).comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv T t)).restrictScalars ℝ)) t := by
    have hd : DifferentiableAt ℝ (fderiv ℝ φ) (T t) :=
      (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp t hT1

  have hT2 : HasFDerivAt (deriv T)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv T) t)).restrictScalars ℝ) t :=
    hT.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hA : HasFDerivAt A ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).comp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv T) t)).restrictScalars ℝ)) t :=
    (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).hasFDerivAt.comp t hT2
  have hG := hc.clm_comp hA
  rw [hfd.fderiv_eq, hG.fderiv]
  simp [hAdef, mul_comm]
  ring

/- English proof (translation)
Introduce `φ T t hφ hT`. Establish `hsymm` using `hφ.isSymmSndFDerivAt (by simp)`. Rewrite using `[laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]`. Simplify using `only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]`. Rewrite using `[fderiv_fderiv_comp_holo_apply φ T t hφ hT, fderiv_fderiv_comp_holo_apply φ T t hφ hT]`.

Use `set D := fderiv ℝ (fderiv ℝ φ) (T t)`. Use `set w := deriv T t`. Establish `hcancel : fderiv ℝ φ (T t) (deriv (deriv T) t * 1 * 1) + fderiv ℝ φ (T t) (deriv (deriv T) t * Complex.I * Complex.I) = 0`. Rewrite using `[← map_add]`. Establish `: deriv (deriv T) t * 1 * 1 + deriv (deriv T) t * Complex.I * Complex.I = 0`.

Rewrite using `[mul_assoc _ Complex.I, Complex.I_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_zero]`. Establish `hw : w * 1 = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Establish `hwI : w * Complex.I = (-w.im : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hs : D 1 Complex.I = D Complex.I 1` using `hsymm 1 Complex.I`. Establish `hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw, hwI, hn]`. Simplify using `only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]`. Take the linear combination `hcancel + (w.re * w.im - w.im * w.re) * hs`.
-/
theorem LaplacianHoloComp.full : LaplacianHoloComp.Statement := by
  intro φ T t hφ hT
  have hsymm := hφ.isSymmSndFDerivAt (by simp)
  rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_comp_holo_apply φ T t hφ hT, fderiv_fderiv_comp_holo_apply φ T t hφ hT]
  set D := fderiv ℝ (fderiv ℝ φ) (T t)
  set w := deriv T t
  have hcancel : fderiv ℝ φ (T t) (deriv (deriv T) t * 1 * 1) +
      fderiv ℝ φ (T t) (deriv (deriv T) t * Complex.I * Complex.I) = 0 := by
    rw [← map_add]
    have : deriv (deriv T) t * 1 * 1 + deriv (deriv T) t * Complex.I * Complex.I = 0 := by
      rw [mul_assoc _ Complex.I, Complex.I_mul_I]; ring
    rw [this, map_zero]
  have hw : w * 1 = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hwI : w * Complex.I = (-w.im : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hs : D 1 Complex.I = D Complex.I 1 := hsymm 1 Complex.I
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hw, hwI, hn]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  linear_combination hcancel + (w.re * w.im - w.im * w.re) * hs
