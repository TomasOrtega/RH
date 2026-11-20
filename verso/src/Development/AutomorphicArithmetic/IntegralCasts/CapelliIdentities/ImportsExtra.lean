import Mathlib

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ A hA hd`. Use `set d := Module.finrank ℝ E with hd_def`. Use `set w : E → ℝ := fun x => ((1 + ‖x‖) ^ A)⁻¹ with hw`. Establish `hwpos : ∀ x, 0 < w x` using `fun x => by`. Establish `: (0:ℝ) < 1 + ‖x‖` using `by positivity`.

Simplify using `only [hw]`. Check the signs of the components of the expression. Establish `hint : MeasureTheory.Integrable w μ`. Establish `h` using `integrable_one_add_norm (E := E) (μ := μ) (r := (A:ℝ)) (by exact_mod_cast hA)`. Use `h.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Establish `: (0:ℝ) < 1 + ‖x‖` using `by positivity`. Simplify using `only [hw]`. Rewrite using `[Real.rpow_neg this.le, Real.rpow_natCast]`. Use `set I : ℝ := ∫ x, w x ∂μ with hI`. Establish `hI0 : 0 ≤ I` using `MeasureTheory.integral_nonneg fun x => (hwpos x).le`.

Use `set V : ℝ := μ.real (Metric.ball (0:E) 1) with hV`. Establish `hVpos : 0 < V`. Use `ENNReal.toReal_pos ?_ ?_` and prove the remaining obligations. Conclude with `(Metric.measure_ball_pos μ 0 one_pos).ne'`. Conclude with `MeasureTheory.measure_ball_lt_top.ne`.

Use `⟨2 ^ A * I / V * 2 ^ d, by positivity, ?_⟩` and prove the remaining obligations. Introduce `η hη F hF`. Establish `hdR : (d:ℝ) ≠ 0` using `by exact_mod_cast hd.ne'`. Use `set r : ℝ := η ^ ((d:ℝ)⁻¹) with hr`. Establish `hrpos : 0 < r` using `Real.rpow_pos_of_pos hη _`.

Establish `hrd : r ^ d = η`. Rewrite using `[hr, ← Real.rpow_natCast, ← Real.rpow_mul hη.le, inv_mul_cancel₀ hdR, Real.rpow_one]`. Use `set s : ℝ := min (r / 2) 1 with hs`. Establish `hspos : 0 < s` using `lt_min (by positivity) one_pos`. Establish `hs1 : s ≤ 1` using `min_le_right _ _`.

Establish `hs2 : 2 * s ≤ r`. Establish `: s ≤ r / 2` using `min_le_left _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkey : 1 ≤ s ^ d * (2 ^ d * (1 + η⁻¹))`. Establish `hη' : 0 < η⁻¹` using `inv_pos.mpr hη`.

Break down `le_total (r / 2) 1 with h | h` into its components or cases. Establish `: s = r / 2` using `min_eq_left h`. Rewrite using `[this, div_pow, hrd]`. Establish `h2 : (2:ℝ) ^ d ≠ 0` using `by positivity`. Establish `: η / 2 ^ d * (2 ^ d * (1 + η⁻¹)) = η + 1`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: s = 1` using `min_eq_right h`. Rewrite using `[this, one_pow, one_mul]`.

Establish `: (1:ℝ) ≤ 2 ^ d` using `one_le_pow₀ (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hball : ∀ y : E, μ.real (Metric.ball y s) = s ^ d * V`. Introduce `y`. Use `MeasureTheory.Measure.addHaar_ball_of_pos μ y hspos` as an intermediate fact.

Simplify using `only [MeasureTheory.Measure.real, hV]`. Rewrite using `[this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Establish `hcomp : ∀ y x : E, x ∈ Metric.ball y s → (2 ^ A)⁻¹ * w y ≤ w x`. Introduce `y x hx`. Establish `hxy : ‖x‖ ≤ ‖y‖ + s`.

Establish `h1 : ‖x - y‖ < s` using `by simpa [dist_eq_norm] using hx`. Establish `h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖`. Use `norm_add_le y (x - y)` as an intermediate fact. Simplify using `using this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hle : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖)`. Use `norm_nonneg y` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx0 : (0:ℝ) < 1 + ‖x‖` using `by positivity`. Establish `hy0 : (0:ℝ) < 1 + ‖y‖` using `by positivity`.

Establish `hp : (1 + ‖x‖) ^ A ≤ 2 ^ A * (1 + ‖y‖) ^ A`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hx0.le hle A`. Simplify using `only [hw]`. Rewrite using `[← mul_inv]`.

Conclude with `inv_anti₀ (by positivity) hp`. Establish `hone : ∀ y : E, (2 ^ A)⁻¹ * w y * (s ^ d * V) ≤ ∫ x in Metric.ball y s, w x ∂μ`. Introduce `y`. Use `MeasureTheory.setIntegral_ge_of_const_le_real (μ := μ) (f := w) (c := (2 ^ A)⁻¹ * w y) (s := Metric.ball y s) Metric.isOpen_ball.measurableSet MeasureTheory.measure_ball_lt_top.ne (fun x hx => hcomp y x hx) hint.integrableOn` as an intermediate fact. Rewrite `this` using `[hball]`.

Conclude with `this`. Establish `hdisj : Set.Pairwise (F : Set E) (Function.onFun Disjoint fun y => Metric.ball y s)`. Introduce `y hy y' hy' hne`. Use `Metric.ball_disjoint_ball ?_` and prove the remaining obligations. Establish `h1` using `hF y hy y' hy' hne`.

Establish `h2 : r ≤ ‖y - y'‖`. Rewrite `h1` using `[← hrd]`. Conclude with `le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) h1`. Rewrite using `[dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsum : ∑ y ∈ F, ∫ x in Metric.ball y s, w x ∂μ ≤ I`. Rewrite using `[← MeasureTheory.integral_biUnion_finset F (fun y _ => Metric.isOpen_ball.measurableSet) hdisj (fun y _ => hint.integrableOn)]`. Conclude with `MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => (hwpos x).le)`. Establish `htot : (2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y ≤ I`. Use `le_trans ?_ hsum` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun y _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hS0 : 0 ≤ ∑ y ∈ F, w y` using `Finset.sum_nonneg fun y _ => (hwpos y).le`. Establish `hsd : 0 < s ^ d` using `by positivity`.

Establish `hfin : ∑ y ∈ F, w y ≤ 2 ^ A * I / V * (1 / s ^ d)`. Establish `h2 : (0:ℝ) < 2 ^ A` using `by positivity`. Rewrite using `[show 2 ^ A * I / V * (1 / s ^ d) = (2 ^ A * I) / (s ^ d * V) by field_simp]`. Rewrite using `[le_div_iff₀ (by positivity)]`. Use `mul_le_mul_of_nonneg_left htot h2.le` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `hinv : 1 / s ^ d ≤ 2 ^ d * (1 + η⁻¹)`. Rewrite using `[div_le_iff₀ hsd]`. Combine the linear relations using `[hkey, mul_comm (s ^ d) (2 ^ d * (1 + η⁻¹))]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Reformulated.B.DYga2.main.{u_1} :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [inst_3 : MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {A : ℕ},
      Module.finrank ℝ E < A →
        (0 : ℕ) < Module.finrank ℝ E →
          ∃ (c : ℝ),
            (0 : ℝ) ≤ c ∧
              ∀ (η : ℝ),
                (0 : ℝ) < η →
                  ∀ (F : Finset E),
                    (∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → η ≤ ‖y - y'‖ ^ Module.finrank ℝ E) →
                      ∑ y ∈ F, (((1 : ℝ) + ‖y‖) ^ A)⁻¹ ≤ c * ((1 : ℝ) + η⁻¹) := by
  intro E _ _ _ _ _ μ _ A hA hd
  set d := Module.finrank ℝ E with hd_def

  set w : E → ℝ := fun x => ((1 + ‖x‖) ^ A)⁻¹ with hw
  have hwpos : ∀ x, 0 < w x := fun x => by
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]; positivity
  have hint : MeasureTheory.Integrable w μ := by
    have h := integrable_one_add_norm (E := E) (μ := μ) (r := (A:ℝ)) (by exact_mod_cast hA)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]
    rw [Real.rpow_neg this.le, Real.rpow_natCast]
  set I : ℝ := ∫ x, w x ∂μ with hI
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun x => (hwpos x).le
  set V : ℝ := μ.real (Metric.ball (0:E) 1) with hV
  have hVpos : 0 < V := by
    refine ENNReal.toReal_pos ?_ ?_
    · exact (Metric.measure_ball_pos μ 0 one_pos).ne'
    · exact MeasureTheory.measure_ball_lt_top.ne
  refine ⟨2 ^ A * I / V * 2 ^ d, by positivity, ?_⟩
  intro η hη F hF
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set r : ℝ := η ^ ((d:ℝ)⁻¹) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hη _
  have hrd : r ^ d = η := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hη.le, inv_mul_cancel₀ hdR, Real.rpow_one]
  set s : ℝ := min (r / 2) 1 with hs
  have hspos : 0 < s := lt_min (by positivity) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hs2 : 2 * s ≤ r := by
    have : s ≤ r / 2 := min_le_left _ _
    linarith

  have hkey : 1 ≤ s ^ d * (2 ^ d * (1 + η⁻¹)) := by
    have hη' : 0 < η⁻¹ := inv_pos.mpr hη
    rcases le_total (r / 2) 1 with h | h
    · have : s = r / 2 := min_eq_left h
      rw [this, div_pow, hrd]
      have h2 : (2:ℝ) ^ d ≠ 0 := by positivity
      have : η / 2 ^ d * (2 ^ d * (1 + η⁻¹)) = η + 1 := by
        field_simp
      rw [this]; linarith
    · have : s = 1 := min_eq_right h
      rw [this, one_pow, one_mul]
      have : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith

  have hball : ∀ y : E, μ.real (Metric.ball y s) = s ^ d * V := by
    intro y
    have := MeasureTheory.Measure.addHaar_ball_of_pos μ y hspos
    simp only [MeasureTheory.Measure.real, hV]
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

  have hcomp : ∀ y x : E, x ∈ Metric.ball y s → (2 ^ A)⁻¹ * w y ≤ w x := by
    intro y x hx
    have hxy : ‖x‖ ≤ ‖y‖ + s := by
      have h1 : ‖x - y‖ < s := by simpa [dist_eq_norm] using hx
      have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
        have := norm_add_le y (x - y)
        simpa using this
      linarith
    have hle : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
      have := norm_nonneg y
      linarith
    have hx0 : (0:ℝ) < 1 + ‖x‖ := by positivity
    have hy0 : (0:ℝ) < 1 + ‖y‖ := by positivity
    have hp : (1 + ‖x‖) ^ A ≤ 2 ^ A * (1 + ‖y‖) ^ A := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hx0.le hle A
    simp only [hw]
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hp

  have hone : ∀ y : E, (2 ^ A)⁻¹ * w y * (s ^ d * V) ≤ ∫ x in Metric.ball y s, w x ∂μ := by
    intro y
    have := MeasureTheory.setIntegral_ge_of_const_le_real (μ := μ) (f := w) (c := (2 ^ A)⁻¹ * w y)
      (s := Metric.ball y s) Metric.isOpen_ball.measurableSet MeasureTheory.measure_ball_lt_top.ne
      (fun x hx => hcomp y x hx) hint.integrableOn
    rw [hball] at this
    exact this

  have hdisj : Set.Pairwise (F : Set E) (Function.onFun Disjoint fun y => Metric.ball y s) := by
    intro y hy y' hy' hne
    refine Metric.ball_disjoint_ball ?_
    have h1 := hF y hy y' hy' hne
    have h2 : r ≤ ‖y - y'‖ := by
      rw [← hrd] at h1
      exact le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) h1
    rw [dist_eq_norm]
    linarith
  have hsum : ∑ y ∈ F, ∫ x in Metric.ball y s, w x ∂μ ≤ I := by
    rw [← MeasureTheory.integral_biUnion_finset F (fun y _ => Metric.isOpen_ball.measurableSet) hdisj
      (fun y _ => hint.integrableOn)]
    exact MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun x => (hwpos x).le)
  have htot : (2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y ≤ I := by
    refine le_trans ?_ hsum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc _ = (2 ^ A)⁻¹ * w y * (s ^ d * V) := by ring
      _ ≤ _ := hone y
  have hS0 : 0 ≤ ∑ y ∈ F, w y := Finset.sum_nonneg fun y _ => (hwpos y).le
  have hsd : 0 < s ^ d := by positivity
  have hfin : ∑ y ∈ F, w y ≤ 2 ^ A * I / V * (1 / s ^ d) := by
    have h2 : (0:ℝ) < 2 ^ A := by positivity
    rw [show 2 ^ A * I / V * (1 / s ^ d) = (2 ^ A * I) / (s ^ d * V) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left htot h2.le
    calc _ = 2 ^ A * ((2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y) := by field_simp
      _ ≤ _ := this
  have hinv : 1 / s ^ d ≤ 2 ^ d * (1 + η⁻¹) := by
    rw [div_le_iff₀ hsd]
    linarith [hkey, mul_comm (s ^ d) (2 ^ d * (1 + η⁻¹))]
  calc ∑ y ∈ F, ((1 + ‖y‖) ^ A)⁻¹ = ∑ y ∈ F, w y := rfl
    _ ≤ 2 ^ A * I / V * (1 / s ^ d) := hfin
    _ ≤ 2 ^ A * I / V * (2 ^ d * (1 + η⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 ^ A * I / V * 2 ^ d * (1 + η⁻¹) := by ring
