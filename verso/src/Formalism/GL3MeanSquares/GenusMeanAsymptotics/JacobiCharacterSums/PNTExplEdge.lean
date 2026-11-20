import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplDefs
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hσp : 0 < σ₁` using `by linarith`. Establish `hB0 : 0 ≤ B` using `le_trans (norm_nonneg _) (hB 0 (by simpa using hT'))`. Establish `hpt : ∀ t ∈ Set.uIoc (-T') T', ‖Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁))`. Introduce `t ht`.

Rewrite `ht` using `[Set.uIoc_of_le (by linarith)]`. Establish `hBt` using `hB t (abs_le.mpr ⟨ht.1.le, ht.2⟩)`. Use `set w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I with hw`. Establish `hre : w.re = σ₁` using `by simp [hw]`. Rewrite using `[norm_perron_integrand_eq χ y hy0 w, hre]`.

Establish `hw1 : σ₁ ≤ ‖w‖`. Use `Complex.abs_re_le_norm w` as an intermediate fact. Rewrite `this` using `[hre, abs_of_pos hσp]`. Conclude with `this`. Establish `hw2 : 1 - σ₁ ≤ ‖w - 1‖`.

Establish `h1 : (w - 1).re = σ₁ - 1` using `by simp [hre]`. Use `Complex.abs_re_le_norm (w - 1)` as an intermediate fact. Rewrite using `[h1, abs_of_neg (by linarith)] at this; linarith`. Establish `hden : σ₁ * (1 - σ₁) ≤ ‖w‖ * ‖w - 1‖` using `mul_le_mul hw1 hw2 (by linarith) (norm_nonneg _)`. Establish `hdp : 0 < σ₁ * (1 - σ₁)` using `mul_pos hσp (by linarith)`.

Establish `hyp : 0 ≤ y ^ σ₁` using `Real.rpow_nonneg hy0.le _`. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `intervalIntegral.norm_integral_le_of_norm_le_const hpt`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `: |T' - -T'| = 2 * T'` using `by rw [abs_of_nonneg (by linarith)]; ring`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_left_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ T' B : ℝ) (hy : 1 ≤ y)
    (hσ : 1 / 2 ≤ σ₁) (hσ1 : σ₁ < 1) (hT' : 0 ≤ T')
    (hB : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in (-T')..T', Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ 2 * T' * B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
  have hy0 : 0 < y := by linarith
  have hσp : 0 < σ₁ := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hT'))
  have hpt : ∀ t ∈ Set.uIoc (-T') T', ‖Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hBt := hB t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
    set w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I with hw
    have hre : w.re = σ₁ := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : σ₁ ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hre, abs_of_pos hσp] at this; exact this
    have hw2 : 1 - σ₁ ≤ ‖w - 1‖ := by
      have h1 : (w - 1).re = σ₁ - 1 := by simp [hre]
      have := Complex.abs_re_le_norm (w - 1)
      rw [h1, abs_of_neg (by linarith)] at this; linarith
    have hden : σ₁ * (1 - σ₁) ≤ ‖w‖ * ‖w - 1‖ :=
      mul_le_mul hw1 hw2 (by linarith) (norm_nonneg _)
    have hdp : 0 < σ₁ * (1 - σ₁) := mul_pos hσp (by linarith)
    have hyp : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ σ₁ / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₁ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) :=
          div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) hdp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  have : |T' - -T'| = 2 * T' := by rw [abs_of_nonneg (by linarith)]; ring
  rw [this]; ring

/- English proof (translation)
Establish `hy0 : 0 < y` using `by linarith`. Establish `hpt : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖Fchi χ y ((x : ℂ) + v * I)‖ ≤ B * y ^ σ₀ / v ^ 2`. Introduce `x hx`. Rewrite `hx` using `[Set.uIoc_of_le hσ]`. Establish `hBx` using `hB x hx.1.le hx.2`.

Use `set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw`. Establish `hre : w.re = x` using `by simp [hw]`. Establish `him : w.im = v` using `by simp [hw]`. Rewrite using `[norm_perron_integrand_eq χ y hy0 w, hre]`. Establish `hw1 : |v| ≤ ‖w‖` using `by rw [← him]; exact Complex.abs_im_le_norm w`.

Establish `hw2 : |v| ≤ ‖w - 1‖`. Establish `: (w - 1).im = v` using `by simp [him]`. Rewrite using `[← this]`. Conclude with `Complex.abs_im_le_norm _`. Establish `hpow : y ^ x ≤ y ^ σ₀` using `Real.rpow_le_rpow_of_exponent_le hy hx.2`.

Establish `hden : v ^ 2 ≤ ‖w‖ * ‖w - 1‖`. Rewrite using `[← sq_abs]`. Use polynomial arithmetic with `[abs_nonneg v]`. Establish `htp : 0 < v ^ 2` using `by rw [← sq_abs]; positivity`. Establish `hyp : 0 ≤ y ^ σ₀` using `Real.rpow_nonneg hy0.le _`.

Combine the equalities or inequalities in the displayed calculation. Establish `h` using `intervalIntegral.norm_integral_le_of_norm_le_const hpt`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[abs_of_nonneg (by linarith)]; ring`.
-/
theorem ex_horiz_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ σ₀ v B : ℝ) (hy : 1 ≤ y)
    (hσ : σ₁ ≤ σ₀) (hv : 1 ≤ |v|) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ B) :
    ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤ (σ₀ - σ₁) * B * y ^ σ₀ / v ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hpt : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖Fchi χ y ((x : ℂ) + v * I)‖ ≤ B * y ^ σ₀ / v ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hσ] at hx
    have hBx := hB x hx.1.le hx.2
    set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
    have hre : w.re = x := by simp [hw]
    have him : w.im = v := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : |v| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
    have hw2 : |v| ≤ ‖w - 1‖ := by
      have : (w - 1).im = v := by simp [him]
      rw [← this]; exact Complex.abs_im_le_norm _
    have hpow : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx.2
    have hden : v ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg v]
    have htp : 0 < v ^ 2 := by rw [← sq_abs]; positivity
    have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ x / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₀ / v ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) htp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith)]; ring

/- English proof (translation)
Establish `hint : MeasureTheory.IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Set.Ioi T)` using `(integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K`. Establish `h` using `MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T)) (f := f) hint ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => by`. Establish `ht0 : 0 < t` using `lt_trans hT ht`. Use `hf t ht` as an intermediate fact. Rewrite using `[Real.rpow_neg ht0.le, Real.rpow_two]`.

Simplify `this)))` using `[div_eq_mul_inv]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]`. Establish `: (-2 : ℝ) + 1 = -1` using `by norm_num`. Rewrite using `[this, Real.rpow_neg_one]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem ex_tail_half (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < t → ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Set.Ioi T, f t‖ ≤ K / T := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have h := MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T))
    (f := f) hint
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => by
      have ht0 : 0 < t := lt_trans hT ht
      have := hf t ht
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      simpa [div_eq_mul_inv] using this)))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
  have : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

/- English proof (translation)
Establish `h1 : (∫ t in Set.Iic (-T), f t) + ∫ t in Set.Ioi (-T), f t = ∫ t : ℝ, f t` using `intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn`. Establish `h2 : (∫ t in (-T)..T, f t) + ∫ t in Set.Ioi T, f t = ∫ t in Set.Ioi (-T), f t` using `intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn`. Establish `h3 : (∫ t in Set.Ioi T, f (-t)) = ∫ t in Set.Iic (-T), f t` using `integral_comp_neg_Ioi T f`. Establish `e : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t = (∫ t in Set.Ioi T, f (-t)) + ∫ t in Set.Ioi T, f t`. Rewrite using `[← h1, ← h2, h3]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `a` using `ex_tail_half (fun t => f (-t)) K T hT (fun t ht => by`. Use `hf (-t) (by rw [abs_neg]; exact lt_of_lt_of_le ht (le_abs_self t))` as an intermediate fact. Simplify using `using this)`.

Establish `b` using `ex_tail_half f K T hT (fun t ht => hf t (lt_of_lt_of_le ht (le_abs_self t)))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ex_tail_gen (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T) (hi : MeasureTheory.Integrable f)
    (hf : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ K / t ^ 2) :
    ‖(∫ t : ℝ, f t) - ∫ t in (-T)..T, f t‖ ≤ 2 * K / T := by
  have h1 : (∫ t in Set.Iic (-T), f t) + ∫ t in Set.Ioi (-T), f t = ∫ t : ℝ, f t :=
    intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn
  have h2 : (∫ t in (-T)..T, f t) + ∫ t in Set.Ioi T, f t = ∫ t in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn
  have h3 : (∫ t in Set.Ioi T, f (-t)) = ∫ t in Set.Iic (-T), f t := integral_comp_neg_Ioi T f
  have e : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t
      = (∫ t in Set.Ioi T, f (-t)) + ∫ t in Set.Ioi T, f t := by
    rw [← h1, ← h2, h3]; ring
  rw [e]
  have a := ex_tail_half (fun t => f (-t)) K T hT (fun t ht => by
    have := hf (-t) (by rw [abs_neg]; exact lt_of_lt_of_le ht (le_abs_self t))
    simpa using this)
  have b := ex_tail_half f K T hT (fun t ht => hf t (lt_of_lt_of_le ht (le_abs_self t)))
  calc _ ≤ ‖∫ t in Set.Ioi T, f (-t)‖ + ‖∫ t in Set.Ioi T, f t‖ := norm_add_le _ _
    _ ≤ K / T + K / T := add_le_add a b
    _ = 2 * K / T := by ring

/- English proof (translation)
Take `⟨C, hC, hR⟩` from `l_log_deriv_right`. Use `⟨C, hC, ?_⟩` and prove the remaining obligations. Introduce `M _ χ y σ₀ T' hy hσ hT'`. Establish `hy0 : 0 < y` using `by linarith`. Establish `hT0 : 0 < T'` using `by linarith`.

Take `⟨hint, -⟩` from `perron_formula_character M χ y hy σ₀ hσ`. Establish `h` using `ex_tail_gen (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ((1 / (σ₀ - 1) + C) * y ^ σ₀) T' hT0 hint (fun t ht => by`. Establish `ht0 : 0 < |t|` using `lt_trans hT0 ht`. Use `show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _`. Use `set w : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hw`.

Establish `hre : w.re = σ₀` using `by simp [hw]`. Establish `him : w.im = t` using `by simp [hw]`. Rewrite using `[norm_perron_integrand_eq χ y hy0 w, hre]`. Establish `hζ : ‖negLD χ w‖ ≤ 1 / (σ₀ - 1) + C`. Use `hR M χ w (by rw [hre]; exact hσ)` as an intermediate fact.

Rewrite `this` using `[hre]`. Then use the resulting hypothesis. Establish `hw1 : |t| ≤ ‖w‖` using `by rw [← him]; exact Complex.abs_im_le_norm w`. Establish `hw2 : |t| ≤ ‖w - 1‖`. Establish `: (w - 1).im = t` using `by simp [him]`. Rewrite using `[← this]`.

Conclude with `Complex.abs_im_le_norm _`. Establish `hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖`. Rewrite using `[← sq_abs]`. Use polynomial arithmetic with `[abs_nonneg t]`. Establish `htp : 0 < t ^ 2` using `by rw [← sq_abs]; positivity`.

Establish `hnum : 0 ≤ 1 / (σ₀ - 1) + C` using `le_trans (norm_nonneg _) hζ`. Establish `hyp : 0 ≤ y ^ σ₀` using `Real.rpow_nonneg hy0.le _`. Combine the equalities or inequalities in the displayed calculation. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_tail_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₀ T' : ℝ),
    1 ≤ y → 1 < σ₀ → 1 ≤ T' →
    ‖(∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)) - ∫ t in (-T')..T', Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * (1 / (σ₀ - 1) + C) * y ^ σ₀ / T' := by
  obtain ⟨C, hC, hR⟩ := l_log_deriv_right
  refine ⟨C, hC, ?_⟩
  intro M _ χ y σ₀ T' hy hσ hT'
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T' := by linarith
  obtain ⟨hint, -⟩ := perron_formula_character M χ y hy σ₀ hσ
  have h := ex_tail_gen (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ((1 / (σ₀ - 1) + C) * y ^ σ₀) T' hT0 hint
    (fun t ht => by
      have ht0 : 0 < |t| := lt_trans hT0 ht
      show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
      set w : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hw
      have hre : w.re = σ₀ := by simp [hw]
      have him : w.im = t := by simp [hw]
      rw [norm_perron_integrand_eq χ y hy0 w, hre]
      have hζ : ‖negLD χ w‖ ≤ 1 / (σ₀ - 1) + C := by
        have := hR M χ w (by rw [hre]; exact hσ)
        rwa [hre] at this
      have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
      have hw2 : |t| ≤ ‖w - 1‖ := by
        have : (w - 1).im = t := by simp [him]
        rw [← this]; exact Complex.abs_im_le_norm _
      have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have htp : 0 < t ^ 2 := by rw [← sq_abs]; positivity
      have hnum : 0 ≤ 1 / (σ₀ - 1) + C := le_trans (norm_nonneg _) hζ
      have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
      calc ‖negLD χ w‖ * y ^ σ₀ / (‖w‖ * ‖w - 1‖)
          ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
        _ ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / t ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hnum hyp) htp hden)
  refine h.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
