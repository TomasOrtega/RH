import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
open MeasureTheory
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FibLine

open Real Set

/- English proof (translation)
Introduce `g hg`. Use `set F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal r * (g (1 / (1 + r ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + r ^ 2) ^ 2))) with hF`. Establish `hFm : Measurable F`. Simplify using `only [hF]`. Establish `: Measurable fun r : ℝ => g (1 / (1 + r ^ 2))` using `hg.comp (by fun_prop)`.

Use `fun_prop`. Rewrite using `[← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]`. Establish `h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 • (fun x : ℂ => g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2))) (Complex.polarCoord.symm p) = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, F p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2`. Use `setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_` and prove the remaining obligations. Establish `hp1 : 0 < p.1` using `hp.1`.

Establish `hn : ‖Complex.polarCoord.symm p‖ = p.1`. Rewrite using `[Complex.norm_polarCoord_symm, abs_of_pos hp1]`. Simplify using `only [hn, hF, smul_eq_mul, mul_one]`. Rewrite using `[h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul (f := F) (g := fun _ : ℝ => (1 : ℝ≥0∞)) hFm.aemeasurable (by fun_prop)]`. Establish `hang : ∫⁻ _ in Ioo (-π) π, (1 : ℝ≥0∞) = ENNReal.ofReal (2 * π)`.

Rewrite using `[setLIntegral_const, one_mul, Real.volume_Ioo]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hang, ← lintegral_mul_const _ hFm]`. Use `set f : ℝ → ℝ := fun r => 1 / (1 + r ^ 2) with hf`.

Use `set f' : ℝ → ℝ := fun r => -(2 * r) / (1 + r ^ 2) ^ 2 with hf'`. Establish `hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f' x) (Set.Ioi 0) x`. Introduce `x _`. Establish `h : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x`. Simplify using `using ((hasDerivAt_pow 2 x).const_add 1)`.

Establish `hne : (1 + x ^ 2) ≠ 0` using `by positivity`. Establish `hfe : f = fun r : ℝ => (1 + r ^ 2)⁻¹`. Use function extensionality and compare the values at `r`. Simplify using `only [hf, one_div]`. Rewrite using `[hfe]`.

Conclude with `(h.inv hne).hasDerivWithinAt`. Establish `hinj : Set.InjOn f (Set.Ioi 0)`. Introduce `a ha b hb hab`. Simplify using `only [hf, one_div, inv_inj, add_right_inj] at hab`. Establish `ha' : (0:ℝ) < a` using `ha`.

Establish `hb' : (0:ℝ) < b` using `hb`. Use polynomial arithmetic with `[sq_nonneg (a - b), sq_nonneg (a + b)]`. Establish `himg : f '' Set.Ioi 0 = Set.Ioo 0 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, hr, rfl⟩`. Establish `hr' : (0:ℝ) < r` using `hr`. Use `⟨by simp only [hf]; positivity, ?_⟩` and prove the remaining obligations. Simplify using `only [hf, one_div]`. Conclude with `inv_lt_one_of_one_lt₀ (by nlinarith)`.

Introduce and unpack `⟨h0, h1⟩`. Establish `ht : 1 < t⁻¹` using `one_lt_inv_iff₀.2 ⟨h0, h1⟩`. Use `⟨Real.sqrt (t⁻¹ - 1), Real.sqrt_pos.2 (by linarith), ?_⟩` and prove the remaining obligations. Simplify using `only [hf]`. Rewrite using `[Real.sq_sqrt (by linarith)]`.

Simplify using the standard rewrite rules. Establish `hcv` using `lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj g`. Rewrite `hcv` using `[himg]`. Rewrite using `[hcv]`. Use `setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_` and prove the remaining obligations.

Establish `hr' : (0:ℝ) < r` using `hr`. Establish `hpi` using `Real.pi_pos`. Establish `hpos : (0:ℝ) < 1 + r ^ 2` using `by positivity`. Establish `habs : |f' r| = 2 * r / (1 + r ^ 2) ^ 2`. Simplify using `only [hf']`.

Rewrite using `[abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]`. Rewrite using `[habs]`. Simplify using `only [hF, hf]`. Establish `key : ENNReal.ofReal r * ENNReal.ofReal (1 / (Real.pi * (1 + r ^ 2) ^ 2)) * ENNReal.ofReal (2 * π) = ENNReal.ofReal (2 * r / (1 + r ^ 2) ^ 2)`. Rewrite using `[← ENNReal.ofReal_mul hr'.le, ← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_comp_fsDens :
    ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by
  intro g hg
  set F : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal r * (g (1 / (1 + r ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + r ^ 2) ^ 2)))
    with hF
  have hFm : Measurable F := by
    simp only [hF]
    have : Measurable fun r : ℝ => g (1 / (1 + r ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      (fun x : ℂ => g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)))
        (Complex.polarCoord.symm p) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, F p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only [hn, hF, smul_eq_mul, mul_one]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := F) (g := fun _ : ℝ => (1 : ℝ≥0∞)) hFm.aemeasurable (by fun_prop)]
  have hang : ∫⁻ _ in Ioo (-π) π, (1 : ℝ≥0∞) = ENNReal.ofReal (2 * π) := by
    rw [setLIntegral_const, one_mul, Real.volume_Ioo]
    congr 1
    ring
  rw [hang, ← lintegral_mul_const _ hFm]
  set f : ℝ → ℝ := fun r => 1 / (1 + r ^ 2) with hf
  set f' : ℝ → ℝ := fun r => -(2 * r) / (1 + r ^ 2) ^ 2 with hf'
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f' x) (Set.Ioi 0) x := by
    intro x _
    have h : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have hfe : f = fun r : ℝ => (1 + r ^ 2)⁻¹ := by
      funext r
      simp only [hf, one_div]
    rw [hfe]
    exact (h.inv hne).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro a ha b hb hab
    simp only [hf, one_div, inv_inj, add_right_inj] at hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have himg : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : (0:ℝ) < r := hr
      refine ⟨by simp only [hf]; positivity, ?_⟩
      simp only [hf, one_div]
      exact inv_lt_one_of_one_lt₀ (by nlinarith)
    · rintro ⟨h0, h1⟩
      have ht : 1 < t⁻¹ := one_lt_inv_iff₀.2 ⟨h0, h1⟩
      refine ⟨Real.sqrt (t⁻¹ - 1), Real.sqrt_pos.2 (by linarith), ?_⟩
      simp only [hf]
      rw [Real.sq_sqrt (by linarith)]
      simp
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj g
  rw [himg] at hcv
  rw [hcv]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0:ℝ) < r := hr
  have hpi := Real.pi_pos
  have hpos : (0:ℝ) < 1 + r ^ 2 := by positivity
  have habs : |f' r| = 2 * r / (1 + r ^ 2) ^ 2 := by
    simp only [hf']
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs]
  simp only [hF, hf]
  have key : ENNReal.ofReal r * ENNReal.ofReal (1 / (Real.pi * (1 + r ^ 2) ^ 2)) *
      ENNReal.ofReal (2 * π) = ENNReal.ofReal (2 * r / (1 + r ^ 2) ^ 2) := by
    rw [← ENNReal.ofReal_mul hr'.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc ENNReal.ofReal r * (g (1 / (1 + r ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + r ^ 2) ^ 2))) *
        ENNReal.ofReal (2 * π)
      = (ENNReal.ofReal r * ENNReal.ofReal (1 / (Real.pi * (1 + r ^ 2) ^ 2)) *
          ENNReal.ofReal (2 * π)) * g (1 / (1 + r ^ 2)) := by ring
    _ = _ := by rw [key]

end GlobalTheory.FibLine
