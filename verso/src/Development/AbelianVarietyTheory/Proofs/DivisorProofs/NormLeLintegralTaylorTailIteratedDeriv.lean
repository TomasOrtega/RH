import Mathlib
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Distinguish the cases in `hI : IntegrableOn (deriv g) (Ioi a)`. Establish `hint : ∫ x in Ioi a, deriv g x = 0 - g a` using `integral_Ioi_of_hasDerivAt_of_tendsto hg.continuous.continuousWithinAt (fun x _ => (hg x).hasDerivAt) hI hlim`. Rewrite `hint` using `[zero_sub]`. Establish `h1 : ‖g a‖ ≤ ∫ x in Ioi a, ‖deriv g x‖`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `: ∫⁻ t in Ioi a, ‖deriv g t‖ₑ = ∞`. Assume the negation of the conclusion as `hne`. Conclude with `hI ⟨hd.aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩`. Rewrite using `[this]`.

Conclude with `le_top`.
-/
theorem taylorTail_step_one {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → F) (a : ℝ) (hg : Differentiable ℝ g) (hd : Continuous (deriv g))
    (hlim : Tendsto g atTop (𝓝 0)) :
    ENNReal.ofReal ‖g a‖ ≤ ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := by
  by_cases hI : IntegrableOn (deriv g) (Ioi a)
  · have hint : ∫ x in Ioi a, deriv g x = 0 - g a :=
      integral_Ioi_of_hasDerivAt_of_tendsto hg.continuous.continuousWithinAt
        (fun x _ => (hg x).hasDerivAt) hI hlim
    rw [zero_sub] at hint
    have h1 : ‖g a‖ ≤ ∫ x in Ioi a, ‖deriv g x‖ := by
      calc ‖g a‖ = ‖∫ x in Ioi a, deriv g x‖ := by rw [hint, norm_neg]
        _ ≤ ∫ x in Ioi a, ‖deriv g x‖ := norm_integral_le_integral_norm _
    calc ENNReal.ofReal ‖g a‖ ≤ ENNReal.ofReal (∫ x in Ioi a, ‖deriv g x‖) := ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ t in Ioi a, ‖deriv g t‖ₑ := ofReal_integral_norm_eq_lintegral_enorm hI
  · have : ∫⁻ t in Ioi a, ‖deriv g t‖ₑ = ∞ := by
      by_contra hne
      exact hI ⟨hd.aestronglyMeasurable, lt_top_iff_ne_top.mpr hne⟩
    rw [this]; exact le_top

/- English proof (translation)
Establish `hcont : Continuous (fun t : ℝ => t ^ j / (j.factorial : ℝ))` using `by fun_prop`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal]`. Use `congr 1`. Rewrite using `[← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]`. Use `push_cast`.

Rewrite using `[zero_pow (Nat.succ_ne_zero j), sub_zero, div_div, mul_comm]`. Conclude with `(hcont.integrableOn_Icc (a := 0) (b := s)).mono_set Ioo_subset_Icc_self`. Use `filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht`. Conclude with `div_nonneg (pow_nonneg ht.1.le _) (by positivity)`.
-/
theorem taylorTail_inner (j : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ioo (0:ℝ) s, ENNReal.ofReal (t ^ j / (j.factorial : ℝ))
      = ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ j / (j.factorial : ℝ)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
      intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
    push_cast
    rw [zero_pow (Nat.succ_ne_zero j), sub_zero, div_div, mul_comm]
  · exact (hcont.integrableOn_Icc (a := 0) (b := s)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact div_nonneg (pow_nonneg ht.1.le _) (by positivity)

/- English proof (translation)
Use `set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) with hw`. Establish `hwm : Measurable w` using `by fun_prop`. Set `G : ℝ → ℝ → ℝ≥0∞` to `fun t s => w t * (Ioi t).indicator f s`. Establish `hG : Measurable (Function.uncurry G)`. Establish `hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2}` using `measurableSet_lt measurable_fst measurable_snd`.

Establish `: Function.uncurry G = fun p : ℝ × ℝ => w p.1 * ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.2) p)`. Use extensionality with `⟨t, s⟩`. Simplify using `only [Function.uncurry_apply_pair, G, Set.indicator, mem_Ioi, mem_setOf_eq]`. Rewrite using `[this]`. Conclude with `(hwm.comp measurable_fst).mul ((hf.comp measurable_snd).indicator hS)`.

Establish `step1 : ∫⁻ t in Ioi (0:ℝ), w t * ∫⁻ s in Ioi t, f s = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), G t s`. Use `setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)` and prove the remaining obligations. Simplify using `only [G]`. Rewrite using `[lintegral_const_mul _ (hf.indicator measurableSet_Ioi), lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr (le_of_lt (mem_Ioi.mp ht))]`. Rewrite using `[step1, lintegral_lintegral_swap hG.aemeasurable]`.

Use `setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)` and prove the remaining obligations. Establish `: ∀ t, G t s = (Iio s).indicator w t * f s`. Introduce `t`. Apply the tactic sequence `by_cases h : t < s <;> simp [G, Set.indicator, h]`. Repeatedly rewrite using `[this]`.

Rewrite using `[lintegral_mul_const _ (hwm.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, taylorTail_inner j s hs]`.
-/
theorem taylorTail_tonelli (f : ℝ → ℝ≥0∞) (hf : Measurable f) (j : ℕ) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ∫⁻ s in Ioi t, f s
      = ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (s ^ (j+1) / ((j+1).factorial : ℝ)) * f s := by
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) with hw
  have hwm : Measurable w := by fun_prop
  let G : ℝ → ℝ → ℝ≥0∞ := fun t s => w t * (Ioi t).indicator f s
  have hG : Measurable (Function.uncurry G) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : Function.uncurry G = fun p : ℝ × ℝ => w p.1 * ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.2) p) := by
      ext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, Set.indicator, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact (hwm.comp measurable_fst).mul ((hf.comp measurable_snd).indicator hS)
  have step1 : ∫⁻ t in Ioi (0:ℝ), w t * ∫⁻ s in Ioi t, f s
      = ∫⁻ t in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), G t s := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [G]
    rw [lintegral_const_mul _ (hf.indicator measurableSet_Ioi), lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr (le_of_lt (mem_Ioi.mp ht))]
  rw [step1, lintegral_lintegral_swap hG.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have : ∀ t, G t s = (Iio s).indicator w t * f s := by
    intro t
    by_cases h : t < s <;> simp [G, Set.indicator, h]
  simp_rw [this]
  rw [lintegral_mul_const _ (hwm.indicator measurableSet_Iio), lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi, taylorTail_inner j s hs]

/- English proof (translation)
Establish `hdiff : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h)` using `fun n => hh.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)`. Establish `hcont : ∀ n : ℕ, Continuous (iteratedDeriv n h)` using `fun n => (hdiff n).continuous`. Establish `key : ∀ j ≤ m, ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `_`. Use `taylorTail_step_one h 0 (hdiff 0) (by rw [← iteratedDeriv_one]; exact hcont 1) (by simpa using hlim 0 (Nat.zero_le _))` as an intermediate fact. Simplify `this` using `[iteratedDeriv_one]`. Consider the case `succ j ih`.

Introduce `hj`. Use `(ih (Nat.le_of_succ_le hj)).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono (fun t => ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (zero_le')` and prove the remaining obligations.

Use `taylorTail_step_one (iteratedDeriv (j+1) h) t (hdiff _) (by rw [← iteratedDeriv_succ]; exact hcont _) (hlim (j+1) hj)` as an intermediate fact. Simplify `this` using `[iteratedDeriv_succ]`. Use `_ = _ := taylorTail_tonelli _ ((hcont _).enorm.measurable) j`. Conclude with `key m le_rfl`.
-/
theorem taylorTail_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (h : ℝ → F) (m : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hlim : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)) :
    ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ m / (m.factorial : ℝ)) * ‖iteratedDeriv (m + 1) h t‖ₑ := by
  have hdiff : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h) := fun n =>
    hh.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
  have hcont : ∀ n : ℕ, Continuous (iteratedDeriv n h) := fun n => (hdiff n).continuous
  have key : ∀ j ≤ m, ENNReal.ofReal ‖h 0‖ ≤ ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ := by
    intro j
    induction j with
    | zero =>
      intro _
      have := taylorTail_step_one h 0 (hdiff 0) (by rw [← iteratedDeriv_one]; exact hcont 1)
        (by simpa using hlim 0 (Nat.zero_le _))
      simpa [iteratedDeriv_one] using this
    | succ j ih =>
      intro hj
      refine (ih (Nat.le_of_succ_le hj)).trans ?_
      calc ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) * ‖iteratedDeriv (j + 1) h t‖ₑ
          ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ j / (j.factorial : ℝ)) *
              ∫⁻ s in Ioi t, ‖iteratedDeriv (j + 1 + 1) h s‖ₑ := by
            refine lintegral_mono (fun t => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (zero_le')
            have := taylorTail_step_one (iteratedDeriv (j+1) h) t (hdiff _)
              (by rw [← iteratedDeriv_succ]; exact hcont _) (hlim (j+1) hj)
            simpa [iteratedDeriv_succ] using this
        _ = _ := taylorTail_tonelli _ ((hcont _).enorm.measurable) j
  exact key m le_rfl

end GlobalTheory
