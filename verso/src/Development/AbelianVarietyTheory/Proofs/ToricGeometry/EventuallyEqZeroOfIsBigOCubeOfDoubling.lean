import Mathlib

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Use `set M : E → ℝ := fun w => ‖F w‖ + ‖F (-w)‖ with hM`. Establish `step : ∀ w : E, ‖w‖ < ε → M ((2 : ℂ) • w) ≤ 4 * M w`. Introduce `w hw`. Establish `h1` using `(hP w hw).2`. Establish `h2` using `(hP (-w) (by rwa [norm_neg])).2`.

Rewrite `h2` using `[neg_neg]`. Simplify using `only [hM]`. Rewrite using `[← smul_neg, h1, h2]`. Establish `e1 : ‖3 * F w + F (-w)‖ ≤ 3 * ‖F w‖ + ‖F (-w)‖` using `(norm_add_le _ _).trans (by simp)`. Establish `e2 : ‖3 * F (-w) + F w‖ ≤ 3 * ‖F (-w)‖ + ‖F w‖` using `(norm_add_le _ _).trans (by simp)`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set w : ℕ → E := fun n => ((2 : ℂ)⁻¹) ^ n • z with hw`. Establish `hnorm : ∀ n, ‖w n‖ = ((2 : ℝ) ^ n)⁻¹ * ‖z‖`. Introduce `n`. Simplify using `[hw, norm_smul]`.

Establish `hsmall : ∀ n, ‖w n‖ < ε`. Introduce `n`. Rewrite using `[hnorm]`. Establish `h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsucc : ∀ n, w n = (2 : ℂ) • w (n + 1)`. Introduce `n`. Simplify using `only [hw, smul_smul]`. Use `congr 1`. Rewrite using `[pow_succ]`.

Clear the denominators using the available nonvanishing facts. Establish `hiter : ∀ n : ℕ, M z ≤ 4 ^ n * M (w n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [hw]`.

Consider the case `succ n ih`. Combine the equalities or inequalities in the displayed calculation. Conclude with `step _ (hsmall _)`. Use `_ = 4 ^ (n + 1) * M (w (n + 1)) := by ring`. Establish `hbound : ∀ n : ℕ, M z ≤ (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n`.

Introduce `n`. Establish `hb : M (w n) ≤ 2 * C * ‖w n‖ ^ 3`. Establish `a1` using `(hP (w n) (hsmall n)).1`. Establish `a2` using `(hP (-w n) (by rw [norm_neg]; exact hsmall n)).1`. Rewrite `a2` using `[norm_neg]`.

Simplify using `only [hM]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2`. Rewrite using `[← pow_mul, mul_comm, pow_mul]`. Evaluate the numerical expressions.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Rewrite using `[hnorm, h4]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(C * ‖z‖ ^ 3)) * h2`. Establish `hlim : Filter.Tendsto (fun n : ℕ => (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n) Filter.atTop (𝓝 0)`. Use `(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul (2 * C * ‖z‖ ^ 3)` as an intermediate fact. Simplify using `using this`.

Establish `hM0 : M z ≤ 0` using `ge_of_tendsto' hlim hbound`. Establish `: ‖F z‖ ≤ 0`. Use `norm_nonneg (F (-z))` as an intermediate fact. Simplify using `only [hM] at hM0`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `norm_le_zero_iff.1 this`.
-/
private lemma eq_zero_of_cube_bound_of_doubling {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E → ℂ) (ε C : ℝ)
    (hP : ∀ w : E, ‖w‖ < ε → ‖F w‖ ≤ C * ‖w‖ ^ 3 ∧ F ((2 : ℂ) • w) = 3 * F w + F (-w))
    (z : E) (hz : ‖z‖ < ε) : F z = 0 := by

  set M : E → ℝ := fun w => ‖F w‖ + ‖F (-w)‖ with hM
  have step : ∀ w : E, ‖w‖ < ε → M ((2 : ℂ) • w) ≤ 4 * M w := by
    intro w hw
    have h1 := (hP w hw).2
    have h2 := (hP (-w) (by rwa [norm_neg])).2
    rw [neg_neg] at h2
    simp only [hM]
    rw [← smul_neg, h1, h2]
    have e1 : ‖3 * F w + F (-w)‖ ≤ 3 * ‖F w‖ + ‖F (-w)‖ :=
      (norm_add_le _ _).trans (by simp)
    have e2 : ‖3 * F (-w) + F w‖ ≤ 3 * ‖F (-w)‖ + ‖F w‖ :=
      (norm_add_le _ _).trans (by simp)
    linarith
  set w : ℕ → E := fun n => ((2 : ℂ)⁻¹) ^ n • z with hw
  have hnorm : ∀ n, ‖w n‖ = ((2 : ℝ) ^ n)⁻¹ * ‖z‖ := by
    intro n
    simp [hw, norm_smul]
  have hsmall : ∀ n, ‖w n‖ < ε := by
    intro n
    rw [hnorm]
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc ((2 : ℝ) ^ n)⁻¹ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < ε := by simpa using hz
  have hsucc : ∀ n, w n = (2 : ℂ) • w (n + 1) := by
    intro n
    simp only [hw, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hiter : ∀ n : ℕ, M z ≤ 4 ^ n * M (w n) := by
    intro n
    induction n with
    | zero => simp [hw]
    | succ n ih =>
      calc M z ≤ 4 ^ n * M (w n) := ih
        _ = 4 ^ n * M ((2 : ℂ) • w (n + 1)) := by rw [← hsucc]
        _ ≤ 4 ^ n * (4 * M (w (n + 1))) := by
          gcongr
          exact step _ (hsmall _)
        _ = 4 ^ (n + 1) * M (w (n + 1)) := by ring
  have hbound : ∀ n : ℕ, M z ≤ (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
    intro n
    have hb : M (w n) ≤ 2 * C * ‖w n‖ ^ 3 := by
      have a1 := (hP (w n) (hsmall n)).1
      have a2 := (hP (-w n) (by rw [norm_neg]; exact hsmall n)).1
      rw [norm_neg] at a2
      simp only [hM]
      linarith
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc M z ≤ 4 ^ n * M (w n) := hiter n
      _ ≤ 4 ^ n * (2 * C * ‖w n‖ ^ 3) := by gcongr
      _ = (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
        have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
          rw [← mul_pow]
          norm_num
        rw [hnorm, h4]
        field_simp
        linear_combination (-(C * ‖z‖ ^ 3)) * h2
  have hlim : Filter.Tendsto (fun n : ℕ => (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n)
      Filter.atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 * C * ‖z‖ ^ 3)
    simpa using this
  have hM0 : M z ≤ 0 := ge_of_tendsto' hlim hbound
  have : ‖F z‖ ≤ 0 := by
    have := norm_nonneg (F (-z))
    simp only [hM] at hM0
    linarith
  exact norm_le_zero_iff.1 this

/- English proof (translation)
Introduce `E _ _ F hO hrel`. Take `⟨C, hC⟩` from `hO.bound`. Establish `hev : ∀ᶠ z in 𝓝 (0 : E), ‖F z‖ ≤ C * ‖z‖ ^ 3 ∧ F ((2 : ℂ) • z) = 3 * F z + F (-z)` using `by filter_upwards [hC, hrel] with z h1 h2`. Conclude with `⟨by simpa using h1, h2⟩`. Take `⟨ε, hε, hP⟩` from `Metric.eventually_nhds_iff.1 hev`.

Use `filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with z hz`. Conclude with `eq_zero_of_cube_bound_of_doubling F ε C (fun w hw => hP (by simpa using hw)) z (by simpa using hz)`.
-/
theorem eventually_eq_zero_of_isBigO_cube_of_doubling :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ),
      F =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) := by
  intro E _ _ F hO hrel
  obtain ⟨C, hC⟩ := hO.bound
  have hev : ∀ᶠ z in 𝓝 (0 : E), ‖F z‖ ≤ C * ‖z‖ ^ 3 ∧ F ((2 : ℂ) • z) = 3 * F z + F (-z) := by
    filter_upwards [hC, hrel] with z h1 h2
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with z hz
  exact eq_zero_of_cube_bound_of_doubling F ε C (fun w hw => hP (by simpa using hw)) z
    (by simpa using hz)

end GlobalTheory
