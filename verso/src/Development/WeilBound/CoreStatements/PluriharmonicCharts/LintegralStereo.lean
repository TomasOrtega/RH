import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates

namespace PositivityTheory.Xgp.fib_stereo

open MeasureTheory Set GroundTheory.Heights₂.Heights.FlagBundles
open scoped ENNReal NNReal

noncomputable section

def ht (ρ : ℝ) : ℝ := (1 - ρ ^ 2) / (1 + ρ ^ 2)

def nF (a : ℂ) : Fin 3 → ℝ :=
  fun i => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def nE (a : ℂ) : E3 := WithLp.toLp 2 (nF a)

def wt (a : ℂ) : ℝ := Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> simp [nF] <;> fun_prop (disch := (intro x; positivity))`.
-/
theorem continuous_nF : Continuous nF := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [nF] <;> fun_prop (disch := (intro x; positivity))

/- English proof (translation)
The claim follows from `((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp continuous_nF).measurable`.
-/
theorem measurable_nE : Measurable nE :=
  ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp continuous_nF).measurable

/- English proof (translation)
Use `set a := Complex.polarCoord.symm (ρ, θ) with ha`. Establish `hn : ‖a‖ ^ 2 = ρ ^ 2`. Rewrite using `[ha, Complex.norm_polarCoord_symm, sq_abs]`. Establish `hre : a.re = ρ * Real.cos θ` using `by rw [ha]; simp [Complex.cos_ofReal_re]`. Establish `him : a.im = ρ * Real.sin θ` using `by rw [ha]; simp [Complex.sin_ofReal_re]`.

Establish `hpos : (0 : ℝ) < 1 + ρ ^ 2` using `by positivity`. Establish `hsq : Real.sqrt (1 - ht ρ ^ 2) = 2 * ρ / (1 + ρ ^ 2)`. Rewrite using `[show 1 - ht ρ ^ 2 = (2 * ρ / (1 + ρ ^ 2)) ^ 2 by unfold ht; field_simp; ring]`. Conclude with `Real.sqrt_sq (by positivity)`. Unfold `nE spherePoint`.

Use extensionality with `i`. Use `fin_cases i`. Use `show 2 * a.re / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.cos θ`. Rewrite using `[hre, hn, hsq]`. Expand and normalize the polynomial expressions, which then agree.

Use `show 2 * a.im / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.sin θ`. Rewrite using `[him, hn, hsq]`. Expand and normalize the polynomial expressions, which then agree. Use `show (1 - ‖a‖ ^ 2) / (1 + ‖a‖ ^ 2) = ht ρ`. Rewrite using `[hn]`.

Both sides reduce to the same expression.
-/
theorem nE_polar {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    nE (Complex.polarCoord.symm (ρ, θ)) = spherePoint (ht ρ) θ := by
  set a := Complex.polarCoord.symm (ρ, θ) with ha
  have hn : ‖a‖ ^ 2 = ρ ^ 2 := by
    rw [ha, Complex.norm_polarCoord_symm, sq_abs]
  have hre : a.re = ρ * Real.cos θ := by rw [ha]; simp [Complex.cos_ofReal_re]
  have him : a.im = ρ * Real.sin θ := by rw [ha]; simp [Complex.sin_ofReal_re]
  have hpos : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  have hsq : Real.sqrt (1 - ht ρ ^ 2) = 2 * ρ / (1 + ρ ^ 2) := by
    rw [show 1 - ht ρ ^ 2 = (2 * ρ / (1 + ρ ^ 2)) ^ 2 by unfold ht; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  unfold nE spherePoint
  ext i
  fin_cases i
  · show 2 * a.re / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.cos θ
    rw [hre, hn, hsq]; ring
  · show 2 * a.im / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.sin θ
    rw [him, hn, hsq]; ring
  · show (1 - ‖a‖ ^ 2) / (1 + ‖a‖ ^ 2) = ht ρ
    rw [hn]; rfl

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ρ, hρ, rfl⟩`. Establish `hρ' : (0 : ℝ) < ρ` using `hρ`. Establish `hp : (0 : ℝ) < 1 + ρ ^ 2` using `by positivity`.

Unfold `ht`. Prove the components needed by the constructor for the conclusion. Rewrite using `[lt_div_iff₀ hp]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[div_lt_one hp]`.

Use the polynomial consequences of the given equalities and inequalities. Introduce and unpack `⟨h1, h2⟩`. Establish `hq : 0 < (1 - y) / (1 + y)` using `div_pos (by linarith) (by linarith)`. Use `⟨Real.sqrt ((1 - y) / (1 + y)), Real.sqrt_pos.2 hq, ?_⟩` and prove the remaining obligations. Unfold `ht`.

Rewrite using `[Real.sq_sqrt hq.le]`. Establish `: (1 : ℝ) + y ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ht_image : ht '' Ioi 0 = Ioo (-1) 1 := by
  ext y
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    have hρ' : (0 : ℝ) < ρ := hρ
    have hp : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
    unfold ht
    constructor
    · rw [lt_div_iff₀ hp]; nlinarith
    · rw [div_lt_one hp]; nlinarith
  · rintro ⟨h1, h2⟩
    have hq : 0 < (1 - y) / (1 + y) := div_pos (by linarith) (by linarith)
    refine ⟨Real.sqrt ((1 - y) / (1 + y)), Real.sqrt_pos.2 hq, ?_⟩
    unfold ht
    rw [Real.sq_sqrt hq.le]
    have : (1 : ℝ) + y ≠ 0 := by linarith
    field_simp
    ring

/- English proof (translation)
Introduce `x hx y hy hxy`. Establish `hx' : (0 : ℝ) < x` using `hx`. Establish `hy' : (0 : ℝ) < y` using `hy`. Unfold `ht at hxy`. Rewrite `hxy` using `[div_eq_div_iff (by positivity) (by positivity)]`.

Establish `h2 : x ^ 2 = y ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[sq_nonneg (x - y), sq_nonneg (x + y)]`.
-/
theorem ht_injOn : InjOn ht (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  unfold ht at hxy
  rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
  have h2 : x ^ 2 = y ^ 2 := by nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/- English proof (translation)
Establish `hp : (1 : ℝ) + ρ ^ 2 ≠ 0` using `by positivity`. Establish `h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * ρ)) ρ`. Simplify using `using (hasDerivAt_pow 2 ρ).const_sub 1`. Establish `h2 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * ρ) ρ`. Simplify using `using (hasDerivAt_pow 2 ρ).const_add 1`.

Use `h1.div h2 hp` as an intermediate fact. Establish `e : (fun x : ℝ => 1 - x ^ 2) / (fun x : ℝ => 1 + x ^ 2) = ht`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression. Rewrite `this` using `[e]`.

Conclude with `this.congr_deriv (by ring)`.
-/
theorem hasDerivAt_ht (ρ : ℝ) : HasDerivAt ht (-(4 * ρ) / (1 + ρ ^ 2) ^ 2) ρ := by
  have hp : (1 : ℝ) + ρ ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * ρ)) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * ρ) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_add 1
  have := h1.div h2 hp
  have e : (fun x : ℝ => 1 - x ^ 2) / (fun x : ℝ => 1 + x ^ 2) = ht := by
    funext x; rfl
  rw [e] at this
  exact this.congr_deriv (by ring)

/- English proof (translation)
Rewrite using `[← ht_image, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi (fun ρ _ => (hasDerivAt_ht ρ).hasDerivWithinAt) ht_injOn G]`. Use `setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)` and prove the remaining obligations. Establish `hρ' : (0 : ℝ) < ρ` using `hρ`. Rewrite using `[neg_div, abs_neg, abs_of_nonneg (by positivity)]`.
-/
theorem lintegral_ht (G : ℝ → ℝ≥0∞) :
    ∫⁻ c in Ioo (-1 : ℝ) 1, G c =
      ∫⁻ ρ in Ioi 0, ENNReal.ofReal (4 * ρ / (1 + ρ ^ 2) ^ 2) * G (ht ρ) := by
  rw [← ht_image, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun ρ _ => (hasDerivAt_ht ρ).hasDerivWithinAt) ht_injOn G]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : (0 : ℝ) < ρ := hρ
  rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]

/- English proof (translation)
Unfold `ht`. Use `fun_prop (disch := (intro x; positivity))`.
-/
theorem continuous_ht : Continuous ht := by
  unfold ht
  fun_prop (disch := (intro x; positivity))

/- English proof (translation)
Establish `hsp` using `SphereLongitudeCoordinates.continuous_spherePoint`. Use `set F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 * (Real.pi⁻¹ / (1 + p.1 ^ 2) ^ 2)) * g (spherePoint (ht p.1) p.2) with hF`. Establish `hFm : Measurable F`. Use `Measurable.mul ?_ ?_` and prove the remaining obligations. Conclude with `ENNReal.measurable_ofReal.comp (by fun_prop)`.

Conclude with `hg.comp (hsp.measurable.comp ((continuous_ht.measurable.comp measurable_fst).prodMk measurable_snd))`. Establish `hC : (ENNReal.ofReal (4 * Real.pi))⁻¹ ≠ ⊤` using `ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne'`. Rewrite using `[← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]`. Establish `h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 • (ENNReal.ofReal (wt (Complex.polarCoord.symm p)) * g (nE (Complex.polarCoord.symm p))) = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F p`. Use `setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)` and prove the remaining obligations.

Take `⟨ρ, θ⟩` from `p`. Establish `hp1 : (0 : ℝ) < ρ` using `hp.1`. Simplify using `only [smul_eq_mul, hF]`. Rewrite using `[nE_polar hp1.le, ← mul_assoc, ← ENNReal.ofReal_mul hp1.le]`. Unfold `wt`.

Rewrite using `[Complex.norm_polarCoord_symm, abs_of_pos hp1]`. Rewrite using `[h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hFm.aemeasurable, lintegral_lintegral_swap hFm.aemeasurable, ← lintegral_const_mul' _ _ hC]`. Use `lintegral_congr fun θ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_ht (fun c => g (spherePoint c θ)), ← lintegral_const_mul' _ _ hC]`. Use `setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)` and prove the remaining obligations.

Establish `hρ' : (0 : ℝ) < ρ` using `hρ`. Simplify using `only [hF]`. Rewrite using `[← mul_assoc]`. Use `congr 1`. Rewrite using `[← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem lintegral_stereo (g : E3 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ a : ℂ, ENNReal.ofReal (wt a) * g (nE a) =
      (ENNReal.ofReal (4 * Real.pi))⁻¹ *
        ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ) := by
  have hsp := SphereLongitudeCoordinates.continuous_spherePoint
  set F : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (p.1 * (Real.pi⁻¹ / (1 + p.1 ^ 2) ^ 2)) * g (spherePoint (ht p.1) p.2) with hF
  have hFm : Measurable F := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact hg.comp (hsp.measurable.comp
        ((continuous_ht.measurable.comp measurable_fst).prodMk measurable_snd))
  have hC : (ENNReal.ofReal (4 * Real.pi))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 •
      (ENNReal.ofReal (wt (Complex.polarCoord.symm p)) * g (nE (Complex.polarCoord.symm p))) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F p := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
    obtain ⟨ρ, θ⟩ := p
    have hp1 : (0 : ℝ) < ρ := hp.1
    simp only [smul_eq_mul, hF]
    rw [nE_polar hp1.le, ← mul_assoc, ← ENNReal.ofReal_mul hp1.le]
    unfold wt
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hFm.aemeasurable,
    lintegral_lintegral_swap hFm.aemeasurable, ← lintegral_const_mul' _ _ hC]
  refine lintegral_congr fun θ => ?_
  rw [lintegral_ht (fun c => g (spherePoint c θ)), ← lintegral_const_mul' _ _ hC]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : (0 : ℝ) < ρ := hρ
  simp only [hF]
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/- English proof (translation)
Establish `h` using `SphereLongitudeCoordinates.toSphere_preimage (s := (univ : Set E3)) MeasurableSet.univ`. Rewrite `h` using `[preimage_univ]`. Rewrite using `[h]`. Simplify using `[Real.volume_Icc, Real.volume_Ioc]`. Rewrite using `[show (1 : ℝ) + 1 = 2 by norm_num, ENNReal.ofReal_ofNat]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem toSphere_univ : (volume : Measure E3).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  have h := SphereLongitudeCoordinates.toSphere_preimage (s := (univ : Set E3)) MeasurableSet.univ
  rw [preimage_univ] at h
  rw [h]
  simp [Real.volume_Icc, Real.volume_Ioc]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, ENNReal.ofReal_ofNat]
  ring

/- English proof (translation)
Use `set h : ℝ → ℝ≥0∞ := fun φ => ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) with hh`. Establish `hper : Function.Periodic h (2 * Real.pi)` using `fun φ => by`. Simplify using `only [hh, SphereLongitudeCoordinates.spherePoint_add_two_pi]`. Establish `: Fact (0 < 2 * Real.pi)` using `⟨by positivity⟩`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show -Real.pi + 2 * Real.pi = Real.pi by ring]`. Rewrite using `[Measure.restrict_congr_set Ioo_ae_eq_Ioc]`. Use `lintegral_congr fun φ => ?_` and prove the remaining obligations. Simplify using `only [hh]`. Rewrite using `[Measure.restrict_congr_set Ioo_ae_eq_Icc]`.

Use `_ = ∫⁻ b : AddCircle (2 * Real.pi), hper.lift b := by`. Rewrite using `[← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi)]`. Both sides reduce to the same expression. Use `_ = ∫⁻ φ in Ioc 0 (0 + 2 * Real.pi), h φ := by`. Rewrite using `[← AddCircle.lintegral_preimage (2 * Real.pi) 0]`.

Both sides reduce to the same expression. Use `_ = _ := by rw [zero_add]`.
-/
theorem per_conv (g : E3 → ℝ≥0∞) :
    ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ) =
      ∫⁻ φ in Ioc 0 (2 * Real.pi), ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) := by
  set h : ℝ → ℝ≥0∞ := fun φ => ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) with hh
  have hper : Function.Periodic h (2 * Real.pi) := fun φ => by
    simp only [hh, SphereLongitudeCoordinates.spherePoint_add_two_pi]
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  calc ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ)
      = ∫⁻ φ in Ioc (-Real.pi) (-Real.pi + 2 * Real.pi), h φ := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        refine lintegral_congr fun φ => ?_
        simp only [hh]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    _ = ∫⁻ b : AddCircle (2 * Real.pi), hper.lift b := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi)]
        rfl
    _ = ∫⁻ φ in Ioc 0 (0 + 2 * Real.pi), h φ := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) 0]
        rfl
    _ = _ := by rw [zero_add]

/- English proof (translation)
Use extensionality with `s hs`. Rewrite using `[Measure.map_apply measurable_nE hs, withDensity_apply _ (measurable_nE hs), Measure.map_apply measurable_subtype_coe hs, sphereMeasure, Measure.smul_apply, smul_eq_mul, SphereLongitudeCoordinates.toSphere_preimage hs, toSphere_univ, ← per_conv, ← lintegral_stereo _ (measurable_o …`. Use `lintegral_congr fun a => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases ha : nE a ∈ s <;> simp [Set.indicator, ha]`.
-/
theorem map_stereo :
    (volume.withDensity fun a : ℂ => ENNReal.ofReal (wt a)).map nE =
      sphereMeasure.map (fun m : Sphere2 => (m : E3)) := by
  ext s hs
  rw [Measure.map_apply measurable_nE hs, withDensity_apply _ (measurable_nE hs),
    Measure.map_apply measurable_subtype_coe hs, sphereMeasure, Measure.smul_apply, smul_eq_mul,
    SphereLongitudeCoordinates.toSphere_preimage hs, toSphere_univ, ← per_conv,
    ← lintegral_stereo _ (measurable_one.indicator hs), ← lintegral_indicator (measurable_nE hs)]
  refine lintegral_congr fun a => ?_
  by_cases ha : nE a ∈ s <;> simp [Set.indicator, ha]

end

end PositivityTheory.Xgp.fib_stereo
