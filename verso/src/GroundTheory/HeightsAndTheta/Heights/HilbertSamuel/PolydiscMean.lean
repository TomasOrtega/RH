import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric Real

noncomputable section

/- English proof (translation)
Establish `h` using `volume_preserving_pi (fun _ : Fin D => (rotation u).measurePreserving)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z j`. Simplify using `[rotation_apply]`.
-/
theorem measurePreserving_circle_smul {D : ℕ} (u : Circle) :
    MeasurePreserving (fun z : Fin D → ℂ => (u : ℂ) • z) := by
  have h := volume_preserving_pi (fun _ : Fin D => (rotation u).measurePreserving)
  convert h using 1
  funext z j
  simp [rotation_apply]

/- English proof (translation)
Establish `he : MeasurableEmbedding (fun z : Fin D → ℂ => (u : ℂ) • z)` using `(Homeomorph.smulOfNeZero (u : ℂ) (Circle.coe_ne_zero u)).measurableEmbedding`. Rewrite using `[← (measurePreserving_circle_smul u).setIntegral_preimage_emb he F]`. Establish `hpre : (fun z : Fin D → ℂ => (u : ℂ) • z) ⁻¹' closedBall 0 ρ = closedBall 0 ρ`. Use extensionality with `z`. Simplify using `[norm_smul, Circle.norm_coe]`.

Rewrite using `[hpre]`.
-/
theorem setIntegral_circle_smul {D : ℕ} (u : Circle) (ρ : ℝ) (F : (Fin D → ℂ) → ℂ) :
    ∫ z in closedBall (0 : Fin D → ℂ) ρ, F ((u : ℂ) • z) =
      ∫ z in closedBall (0 : Fin D → ℂ) ρ, F z := by
  have he : MeasurableEmbedding (fun z : Fin D → ℂ => (u : ℂ) • z) :=
    (Homeomorph.smulOfNeZero (u : ℂ) (Circle.coe_ne_zero u)).measurableEmbedding
  rw [← (measurePreserving_circle_smul u).setIntegral_preimage_emb he F]
  have hpre : (fun z : Fin D → ℂ => (u : ℂ) • z) ⁻¹' closedBall 0 ρ = closedBall 0 ρ := by
    ext z
    simp [norm_smul, Circle.norm_coe]
  rw [hpre]

/- English proof (translation)
Use `set B := closedBall (0 : Fin D → ℂ) ρ with hBdef`. Use `set F : ℝ → (Fin D → ℂ) → ℂ := fun θ z => g (Complex.exp (θ * Complex.I) • z) * (w z : ℂ) with hFdef`. Establish `hnorm : ∀ (θ : ℝ) (z : Fin D → ℂ), ‖Complex.exp (θ * Complex.I) • z‖ = ‖z‖`. Introduce `θ z`. Rewrite using `[norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]`.

Establish `hrotI : ∀ θ : ℝ, ∫ z in B, F θ z = ∫ z in B, g z * (w z : ℂ)`. Introduce `θ`. Use `setIntegral_circle_smul (Circle.exp θ) ρ (fun z => g z * (w z : ℂ))` as an intermediate fact. Simplify using `only [hrot] at this`. Simplify using `only [Circle.coe_exp] at this`.

Conclude with `this`. Establish `hmean : ∀ z ∈ B, ∫ θ in (0 : ℝ)..2 * π, g (Complex.exp (θ * Complex.I) • z) = (2 * π) • g 0`. Introduce `z hz`. Use `set h : ℂ → ℂ := fun ζ => g (ζ • z) with hhdef`. Establish `hh : AnalyticOnNhd ℂ h (closedBall 0 1)`.

Introduce `ζ hζ`. Establish `hmem : ζ • z ∈ B`. Rewrite `hz`, `hζ`, the goal using `[mem_closedBall_zero_iff]`. Rewrite using `[norm_smul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hζ).trans hz`.

Establish `hA : AnalyticAt ℂ (fun ζ : ℂ => ζ • z) ζ` using `((ContinuousLinearMap.id ℂ ℂ).smulRight z).analyticAt ζ`. Conclude with `(hg (ζ • z) hmem).comp_of_eq hA rfl`. Establish `hc : circleAverage h 0 1 = h 0`. Apply `DiffContOnCl.circleAverage` to reduce the goal to its premises. Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises.

Rewrite using `[closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]`. Conclude with `hh.differentiableOn`. Establish `e : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp (θ * Complex.I)`. Introduce `θ`. Simplify using `[circleMap]`.

Rewrite `hc` using `[circleAverage_def]`. Simplify using `only [hhdef, e, zero_smul] at hc`. Rewrite using `[← hc, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]`. Establish `hcont : ContinuousOn (Function.uncurry F) (Icc 0 (2 * π) ×ˢ B)`. Establish `hmaps : MapsTo (fun p : ℝ × (Fin D → ℂ) => Complex.exp (p.1 * Complex.I) • p.2) (Icc 0 (2 * π) ×ˢ B) B`.

Introduce `p hp`. Simplify using `only [hBdef, mem_closedBall_zero_iff, hnorm]`. Conclude with `mem_closedBall_zero_iff.mp hp.2`. Conclude with `(hg.continuousOn.comp (by fun_prop) hmaps).mul (by fun_prop)`. Establish `hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict B))`.

Rewrite using `[Measure.prod_restrict]`. Conclude with `(hcont.integrableOn_compact (μ := volume.prod volume) (isCompact_Icc.prod (isCompact_closedBall 0 ρ))).mono_set (prod_mono Ioc_subset_Icc_self subset_rfl)`. Establish `hswap` using `integral_integral_swap hint`. Establish `h2pi : (2 * π : ℝ) ≠ 0` using `by positivity`. Apply `smul_right_injective ℂ h2pi` to reduce the goal to its premises.

Simplify using `only`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[hrotI]`. Rewrite using `[setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)]`. Use `_ = ∫ z in B, ∫ θ in Ioc 0 (2 * π), F θ z := hswap`.

Use `_ = ∫ z in B, ((2 * π) • g 0) * (w z : ℂ) := by`. Use `setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)` and prove the remaining obligations. Simplify using `only [hFdef]`. Rewrite using `[integral_mul_const, ← intervalIntegral.integral_of_le (by positivity), hmean z hz]`. Use `_ = (2 * π) • (g 0 * ∫ z in B, (w z : ℂ)) := by`.

Rewrite using `[integral_const_mul, smul_mul_assoc]`.
-/
theorem setIntegral_mul_weight_eq {D : ℕ} {ρ : ℝ} {g : (Fin D → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ)) {w : (Fin D → ℂ) → ℝ} (hw : Continuous w)
    (hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z) :
    ∫ z in closedBall (0 : Fin D → ℂ) ρ, g z * (w z : ℂ) =
      g 0 * ∫ z in closedBall (0 : Fin D → ℂ) ρ, (w z : ℂ) := by
  set B := closedBall (0 : Fin D → ℂ) ρ with hBdef
  set F : ℝ → (Fin D → ℂ) → ℂ := fun θ z => g (Complex.exp (θ * Complex.I) • z) * (w z : ℂ)
    with hFdef
  have hnorm : ∀ (θ : ℝ) (z : Fin D → ℂ), ‖Complex.exp (θ * Complex.I) • z‖ = ‖z‖ := by
    intro θ z
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

  have hrotI : ∀ θ : ℝ, ∫ z in B, F θ z = ∫ z in B, g z * (w z : ℂ) := by
    intro θ
    have := setIntegral_circle_smul (Circle.exp θ) ρ (fun z => g z * (w z : ℂ))
    simp only [hrot] at this
    simp only [Circle.coe_exp] at this
    exact this

  have hmean : ∀ z ∈ B, ∫ θ in (0 : ℝ)..2 * π, g (Complex.exp (θ * Complex.I) • z) =
      (2 * π) • g 0 := by
    intro z hz
    set h : ℂ → ℂ := fun ζ => g (ζ • z) with hhdef
    have hh : AnalyticOnNhd ℂ h (closedBall 0 1) := by
      intro ζ hζ
      have hmem : ζ • z ∈ B := by
        rw [mem_closedBall_zero_iff] at hz hζ ⊢
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hζ).trans hz
      have hA : AnalyticAt ℂ (fun ζ : ℂ => ζ • z) ζ :=
        ((ContinuousLinearMap.id ℂ ℂ).smulRight z).analyticAt ζ
      exact (hg (ζ • z) hmem).comp_of_eq hA rfl
    have hc : circleAverage h 0 1 = h 0 := by
      apply DiffContOnCl.circleAverage
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]
      exact hh.differentiableOn
    have e : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by
      intro θ
      simp [circleMap]
    rw [circleAverage_def] at hc
    simp only [hhdef, e, zero_smul] at hc
    rw [← hc, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

  have hcont : ContinuousOn (Function.uncurry F) (Icc 0 (2 * π) ×ˢ B) := by
    have hmaps : MapsTo (fun p : ℝ × (Fin D → ℂ) => Complex.exp (p.1 * Complex.I) • p.2)
        (Icc 0 (2 * π) ×ˢ B) B := by
      intro p hp
      simp only [hBdef, mem_closedBall_zero_iff, hnorm]
      exact mem_closedBall_zero_iff.mp hp.2
    exact (hg.continuousOn.comp (by fun_prop) hmaps).mul (by fun_prop)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact (hcont.integrableOn_compact (μ := volume.prod volume)
      (isCompact_Icc.prod (isCompact_closedBall 0 ρ))).mono_set
      (prod_mono Ioc_subset_Icc_self subset_rfl)
  have hswap := integral_integral_swap hint
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  apply smul_right_injective ℂ h2pi
  simp only
  calc (2 * π) • ∫ z in B, g z * (w z : ℂ)
      = ∫ θ in Ioc 0 (2 * π), ∫ z in B, F θ z := by
        simp_rw [hrotI]
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal (by positivity)]
    _ = ∫ z in B, ∫ θ in Ioc 0 (2 * π), F θ z := hswap
    _ = ∫ z in B, ((2 * π) • g 0) * (w z : ℂ) := by
        refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
        simp only [hFdef]
        rw [integral_mul_const, ← intervalIntegral.integral_of_le (by positivity), hmean z hz]
    _ = (2 * π) • (g 0 * ∫ z in B, (w z : ℂ)) := by
        rw [integral_const_mul, smul_mul_assoc]

/- English proof (translation)
Establish `hmean` using `setIntegral_mul_weight_eq hg hw hrot`. Use `set B := closedBall (0 : Fin D → ℂ) ρ`. Establish `hB : IsCompact B` using `isCompact_closedBall 0 ρ`. Establish `hgc : ContinuousOn g B` using `hg.continuousOn`. Establish `i1 : Integrable (fun z => ‖g z‖ ^ 2 * w z) (volume.restrict B)` using `((hgc.norm.pow 2).mul hw.continuousOn).integrableOn_compact hB`.

Establish `i2 : Integrable w (volume.restrict B)` using `hw.continuousOn.integrableOn_compact hB`. Establish `i3 : Integrable (fun z => g z * (w z : ℂ)) (volume.restrict B)` using `(hgc.mul (Complex.continuous_ofReal.comp hw).continuousOn).integrableOn_compact hB`. Establish `key : 0 ≤ ∫ z in B, ‖g z - g 0‖ ^ 2 * w z` using `setIntegral_nonneg measurableSet_closedBall (fun z _ => mul_nonneg (sq_nonneg _) (hw0 z))`. Establish `expand : ∀ z, ‖g z - g 0‖ ^ 2 * w z = (‖g z‖ ^ 2 * w z + ‖g 0‖ ^ 2 * w z) - 2 * Complex.reCLM (g z * (w z : ℂ) * (starRingEnd ℂ) (g 0))`. Introduce `z`.

Rewrite using `[Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]`. Simplify using `only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[expand]`. Establish `i4 : Integrable (fun z => g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)) (volume.restrict B)` using `i3.mul_const _`.

Rewrite `key` using `[integral_sub (f := fun z => ‖g z‖ ^ 2 * w z + ‖g 0‖ ^ 2 * w z) (g := fun z => 2 * Complex.reCLM (g z * (w z : ℂ) * (starRingEnd ℂ) (g 0))) (i1.add (i2.const_mul _)) ((Complex.reCLM.integrable_comp i4).const_mul 2), integral_add (f := fun z => ‖g z‖ ^ 2 * w z) (g := fun z => ‖g 0 …`. Establish `hre : Complex.reCLM (g 0 * ((∫ z in B, w z : ℝ) : ℂ) * (starRingEnd ℂ) (g 0)) = ‖g 0‖ ^ 2 * ∫ z in B, w z`. Rewrite using `[mul_comm (g 0), mul_assoc, Complex.mul_conj, Complex.reCLM_apply, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.sq_norm, mul_comm]`. Rewrite `key` using `[hre]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sq_norm_mul_setIntegral_le {D : ℕ} {ρ : ℝ} {g : (Fin D → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ)) {w : (Fin D → ℂ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ z, 0 ≤ w z) (hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z) :
    ‖g 0‖ ^ 2 * ∫ z in closedBall (0 : Fin D → ℂ) ρ, w z ≤
      ∫ z in closedBall (0 : Fin D → ℂ) ρ, ‖g z‖ ^ 2 * w z := by
  have hmean := setIntegral_mul_weight_eq hg hw hrot
  set B := closedBall (0 : Fin D → ℂ) ρ
  have hB : IsCompact B := isCompact_closedBall 0 ρ
  have hgc : ContinuousOn g B := hg.continuousOn
  have i1 : Integrable (fun z => ‖g z‖ ^ 2 * w z) (volume.restrict B) :=
    ((hgc.norm.pow 2).mul hw.continuousOn).integrableOn_compact hB
  have i2 : Integrable w (volume.restrict B) := hw.continuousOn.integrableOn_compact hB
  have i3 : Integrable (fun z => g z * (w z : ℂ)) (volume.restrict B) :=
    (hgc.mul (Complex.continuous_ofReal.comp hw).continuousOn).integrableOn_compact hB
  have key : 0 ≤ ∫ z in B, ‖g z - g 0‖ ^ 2 * w z :=
    setIntegral_nonneg measurableSet_closedBall (fun z _ => mul_nonneg (sq_nonneg _) (hw0 z))
  have expand : ∀ z, ‖g z - g 0‖ ^ 2 * w z = (‖g z‖ ^ 2 * w z + ‖g 0‖ ^ 2 * w z) -
      2 * Complex.reCLM (g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)) := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [expand] at key
  have i4 : Integrable (fun z => g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)) (volume.restrict B) :=
    i3.mul_const _
  rw [integral_sub (f := fun z => ‖g z‖ ^ 2 * w z + ‖g 0‖ ^ 2 * w z)
      (g := fun z => 2 * Complex.reCLM (g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)))
      (i1.add (i2.const_mul _)) ((Complex.reCLM.integrable_comp i4).const_mul 2),
    integral_add (f := fun z => ‖g z‖ ^ 2 * w z) (g := fun z => ‖g 0‖ ^ 2 * w z) i1
      (i2.const_mul _), integral_const_mul, integral_const_mul,
    Complex.reCLM.integral_comp_comm i4, integral_mul_const, hmean, integral_complex_ofReal] at key
  have hre : Complex.reCLM (g 0 * ((∫ z in B, w z : ℝ) : ℂ) * (starRingEnd ℂ) (g 0)) =
      ‖g 0‖ ^ 2 * ∫ z in B, w z := by
    rw [mul_comm (g 0), mul_assoc, Complex.mul_conj, Complex.reCLM_apply, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.sq_norm, mul_comm]
  rw [hre] at key
  linarith

/- English proof (translation)
Establish `h0 : ∫ z in closedBall (0 : ℂ) ρ, Real.exp (-c * ‖z‖ ^ 2) = ∫ z : ℂ, (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) ‖z‖`. Rewrite using `[← integral_indicator measurableSet_closedBall]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Apply the tactic sequence `by_cases hz : ‖z‖ ≤ ρ <;> simp [indicator, hz]`.

Rewrite using `[h0, integral_fun_norm_addHaar volume (fun r => (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) r), Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]`. Establish `h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) y = ∫ y in (0 : ℝ)..ρ, y * Real.exp (-c * y ^ 2)`. Establish `: (fun y : ℝ => y ^ (2 - 1) • (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) y) = (Iic ρ).indicator (fun y => y * Real.exp (-c * y ^ 2))`. Use function extensionality and compare the values at `y`. Apply the tactic sequence `by_cases hy : y ≤ ρ <;> simp [indicator, hy]`.

Rewrite using `[this, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, intervalIntegral.integral_of_le hρ]`. Rewrite using `[h1]`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Simplify using `only [if_true]`.

Establish `: ∫ y in (0 : ℝ)..ρ, y * Real.exp (-0 * y ^ 2) = ρ ^ 2 / 2`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using `[nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hc, if_false]`. Establish `hd : ∀ y ∈ uIcc 0 ρ, HasDerivAt (fun y : ℝ => -Real.exp (-c * y ^ 2) / (2 * c)) (y * Real.exp (-c * y ^ 2)) y`. Introduce `y _`. Use `(((hasDerivAt_pow 2 y).const_mul (-c)).exp.neg).div_const (2 * c)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[show (2:ℕ) - 1 = 1 from rfl, pow_one]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by`. Apply `Continuous.intervalIntegrable` to reduce the goal to its premises.

Use the proof step `fun_prop)]`. Simplify using `[nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_closedBall_gauss (c ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫ z in closedBall (0 : ℂ) ρ, Real.exp (-c * ‖z‖ ^ 2) =
      if c = 0 then π * ρ ^ 2 else π * (1 - Real.exp (-c * ρ ^ 2)) / c := by
  have h0 : ∫ z in closedBall (0 : ℂ) ρ, Real.exp (-c * ‖z‖ ^ 2) =
      ∫ z : ℂ, (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) ‖z‖ := by
    rw [← integral_indicator measurableSet_closedBall]
    congr 1
    funext z
    by_cases hz : ‖z‖ ≤ ρ <;> simp [indicator, hz]
  rw [h0, integral_fun_norm_addHaar volume (fun r => (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) y =
      ∫ y in (0 : ℝ)..ρ, y * Real.exp (-c * y ^ 2) := by
    have : (fun y : ℝ => y ^ (2 - 1) • (Iic ρ).indicator (fun r => Real.exp (-c * r ^ 2)) y) =
        (Iic ρ).indicator (fun y => y * Real.exp (-c * y ^ 2)) := by
      funext y
      by_cases hy : y ≤ ρ <;> simp [indicator, hy]
    rw [this, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
      intervalIntegral.integral_of_le hρ]
  rw [h1]
  by_cases hc : c = 0
  · subst hc
    simp only [if_true]
    have : ∫ y in (0 : ℝ)..ρ, y * Real.exp (-0 * y ^ 2) = ρ ^ 2 / 2 := by
      simp
    rw [this]
    simp [nsmul_eq_mul]
    ring
  · simp only [hc, if_false]
    have hd : ∀ y ∈ uIcc 0 ρ, HasDerivAt (fun y : ℝ => -Real.exp (-c * y ^ 2) / (2 * c))
        (y * Real.exp (-c * y ^ 2)) y := by
      intro y _
      have := (((hasDerivAt_pow 2 y).const_mul (-c)).exp.neg).div_const (2 * c)
      refine this.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp [nsmul_eq_mul]
    field_simp
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
