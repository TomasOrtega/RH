import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

/- English proof (translation)
Introduce `N s hN hs F _`. Use `set a : ℝ := -(1 / N) with ha_def`. Establish `ha : a ≠ 0` using `neg_ne_zero.mpr (one_div_ne_zero hN.ne')`. Establish `hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => (t / s) ^ a) (1 / s * a * (t / s) ^ (a - 1)) (Set.Ioi 0) t`. Introduce `t ht`.

Establish `h1 : HasDerivAt (fun y : ℝ => y / s) (1 / s) t` using `(hasDerivAt_id' t).div_const s`. Conclude with `(h1.rpow_const (Or.inl (div_pos ht hs).ne')).hasDerivWithinAt`. Establish `hinj : Set.InjOn (fun t : ℝ => (t / s) ^ a) (Set.Ioi 0)`. Introduce `x hx y hy hxy`. Establish `hxy' : (x / s) ^ a = (y / s) ^ a` using `hxy`.

Establish `hdiv : x / s = y / s`. Rewrite using `[← Real.rpow_rpow_inv (div_pos hx hs).le ha, ← Real.rpow_rpow_inv (div_pos hy hs).le ha, hxy']`. Conclude with `(div_left_inj' hs.ne').mp hdiv`. Establish `himage : (fun t : ℝ => (t / s) ^ a) '' Set.Ioi 0 = Set.Ioi 0`. Use extensionality with `τ`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Conclude with `Real.rpow_pos_of_pos (div_pos ht hs) a`. Introduce `hτ`. Use `⟨s * τ ^ a⁻¹, mul_pos hs (Real.rpow_pos_of_pos hτ _), ?_⟩` and prove the remaining obligations.

Use `show (s * τ ^ a⁻¹ / s) ^ a = τ`. Rewrite using `[mul_div_cancel_left₀ _ hs.ne', Real.rpow_inv_rpow (le_of_lt hτ) ha]`. Establish `key` using `lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj (fun τ => F τ * ENNReal.ofReal (N / τ))`. Rewrite `key` using `[himage]`. Rewrite using `[key]`.

Use `setLIntegral_congr_fun measurableSet_Ioi ?_` and prove the remaining obligations. Introduce `t ht`. Establish `ht' : 0 < t` using `ht`. Establish `hu : 0 < t / s` using `div_pos ht' hs`. Establish `hua : 0 < (t / s) ^ a` using `Real.rpow_pos_of_pos hu a`.

Establish `hreal : |1 / s * a * (t / s) ^ (a - 1)| * (N / (t / s) ^ a) = t⁻¹`. Establish `hneg : 1 / s * a * (t / s) ^ (a - 1) = -(1 / s * (1 / N) * ((t / s) ^ a / (t / s)))`. Rewrite using `[Real.rpow_sub hu, Real.rpow_one, ha_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : 0 < 1 / s * (1 / N) * ((t / s) ^ a / (t / s))` using `mul_pos (mul_pos (one_div_pos.mpr hs) (one_div_pos.mpr hN)) (div_pos hua hu)`.

Rewrite using `[hneg, abs_neg, abs_of_pos hpos]`. Clear the denominators using the available nonvanishing facts. Simplify using `only`. Rewrite using `[div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos ht', ← hreal, ENNReal.ofReal_mul (abs_nonneg _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_rpow_neg_change_of_variable :
    ∀ (N s : ℝ), 0 < N → 0 < s → ∀ F : ℝ → ENNReal, Measurable F →
      ∫⁻ t in Set.Ioi (0 : ℝ), F ((t / s) ^ (-(1 / N))) / ENNReal.ofReal t =
        ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ENNReal.ofReal (N / τ) := by
  intro N s hN hs F _
  set a : ℝ := -(1 / N) with ha_def
  have ha : a ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero hN.ne')

  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => (t / s) ^ a) (1 / s * a * (t / s) ^ (a - 1))
        (Set.Ioi 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => y / s) (1 / s) t := (hasDerivAt_id' t).div_const s
    exact (h1.rpow_const (Or.inl (div_pos ht hs).ne')).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => (t / s) ^ a) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hxy' : (x / s) ^ a = (y / s) ^ a := hxy
    have hdiv : x / s = y / s := by
      rw [← Real.rpow_rpow_inv (div_pos hx hs).le ha, ← Real.rpow_rpow_inv (div_pos hy hs).le ha,
        hxy']
    exact (div_left_inj' hs.ne').mp hdiv
  have himage : (fun t : ℝ => (t / s) ^ a) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.rpow_pos_of_pos (div_pos ht hs) a
    · intro hτ
      refine ⟨s * τ ^ a⁻¹, mul_pos hs (Real.rpow_pos_of_pos hτ _), ?_⟩
      show (s * τ ^ a⁻¹ / s) ^ a = τ
      rw [mul_div_cancel_left₀ _ hs.ne', Real.rpow_inv_rpow (le_of_lt hτ) ha]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun τ => F τ * ENNReal.ofReal (N / τ))
  rw [himage] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := ht
  have hu : 0 < t / s := div_pos ht' hs
  have hua : 0 < (t / s) ^ a := Real.rpow_pos_of_pos hu a

  have hreal : |1 / s * a * (t / s) ^ (a - 1)| * (N / (t / s) ^ a) = t⁻¹ := by
    have hneg : 1 / s * a * (t / s) ^ (a - 1) = -(1 / s * (1 / N) * ((t / s) ^ a / (t / s))) := by
      rw [Real.rpow_sub hu, Real.rpow_one, ha_def]
      ring
    have hpos : 0 < 1 / s * (1 / N) * ((t / s) ^ a / (t / s)) :=
      mul_pos (mul_pos (one_div_pos.mpr hs) (one_div_pos.mpr hN)) (div_pos hua hu)
    rw [hneg, abs_neg, abs_of_pos hpos]
    field_simp
  dsimp only
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos ht', ← hreal,
    ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end GlobalTheory.FlagMeas
