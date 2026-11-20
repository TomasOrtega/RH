import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

namespace GlobalTheory.CompanionTheory.Ar.PB

/- English proof (translation)
Rewrite using `[one_div, Real.log_inv, Real.log_exp, neg_neg]`.
-/
theorem limRate_log_inv_exp (s : ℝ) : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

/- English proof (translation)
Establish `h` using `Real.sum_le_exp_of_nonneg hx 4`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h`. Evaluate the numerical expressions using `at h`. Use polynomial arithmetic with `[mul_nonneg hx (sq_nonneg (x - 3 / 2))]`.
-/
theorem limRate_sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [mul_nonneg hx (sq_nonneg (x - 3 / 2))]

/- English proof (translation)
Establish `h` using `limRate_sq_le_exp (x := -Real.log s) (by linarith [Real.log_nonpos hs.le h1])`. Rewrite `h` using `[Real.exp_neg, Real.exp_log hs, neg_sq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem limRate_mul_log_sq_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : s * Real.log s ^ 2 ≤ 1 := by
  have h := limRate_sq_le_exp (x := -Real.log s) (by linarith [Real.log_nonpos hs.le h1])
  rw [Real.exp_neg, Real.exp_log hs, neg_sq] at h
  calc s * Real.log s ^ 2 ≤ s * s⁻¹ := mul_le_mul_of_nonneg_left h hs.le
    _ = 1 := mul_inv_cancel₀ hs.ne'

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hl : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop`. Simplify using `only [one_div]`. Conclude with `Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero`. Establish `h` using `(Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hl`.

Use `h.congr fun t => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `s hs h1`. Rewrite using `[limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]`. Establish `h3` using `limRate_mul_log_sq_le hs h1`.

Use `push_cast`. Establish `e : (-(2 * Real.log s)) ^ 2 * s ^ 2 = 4 * s * (s * Real.log s ^ 2)` using `by ring`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `s hs h1`.

Rewrite using `[← Real.exp_mul]`. Use `set y := (s ^ 2)⁻¹ with hy`. Establish `hys : y * s ^ 2 = 1` using `inv_mul_cancel₀ (by positivity)`. Establish `hy0 : 0 ≤ y` using `by positivity`. Establish `ha` using `Real.add_one_le_exp (y * (1 / 3))`.

Establish `hE : 0 < Real.exp (y * (1 / 3))` using `Real.exp_pos _`. Rewrite using `[show -y * (1 / 3) = -(y * (1 / 3)) by ring, Real.exp_neg]`. Establish `hkey : 1 ≤ 2 * s * (1 + y * (1 / 3))`. Use polynomial arithmetic with `[sq_nonneg (s - 1 / 4), mul_pos hs hs]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[inv_le_iff_one_le_mul₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `C ε hε set K := 2 * |C| + 1 with hK`. Establish `hKpos : 0 < K` using `by positivity`. Use `⟨min 1 ((ε / K) ^ 2), by positivity, ?_⟩` and prove the remaining obligations.

Introduce `s hs hs0`. Establish `h1 : s ≤ 1` using `le_trans hs0 (min_le_left _ _)`. Establish `h2 : s ≤ (ε / K) ^ 2` using `le_trans hs0 (min_le_right _ _)`. Rewrite using `[limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]`. Use `push_cast`.

Establish `h3` using `limRate_mul_log_sq_le hs h1`. Establish `hsq : (s * Real.log s) ^ 2 ≤ (ε / K) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `habs : |s * Real.log s| ≤ ε / K` using `abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))`. Establish `hb : -2 * C * (s * Real.log s) ≤ ε`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_mul, abs_mul, abs_neg, abs_two]`. Use `_ ≤ 2 * |C| * (ε / K) := mul_le_mul_of_nonneg_left habs (by positivity)`. Use `_ ≤ ε := by`. Rewrite using `[mul_div_assoc', div_le_iff₀ hKpos, hK]`.

Use polynomial arithmetic with `[abs_nonneg C]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem limRate : Filter.Tendsto (fun t : ℝ => Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) ^ 2 / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ 4 * s) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.exp (-(s ^ 2)⁻¹) ^ ((1 : ℝ) / 3) ≤ 2 * s) ∧ ∀ C ε : ℝ, 0 < ε → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → C * Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ ε * s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hl : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simp only [one_div]
      exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hl
    refine h.congr fun t => ?_
    simp
  · intro s hs h1
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    have h3 := limRate_mul_log_sq_le hs h1
    push_cast
    have e : (-(2 * Real.log s)) ^ 2 * s ^ 2 = 4 * s * (s * Real.log s ^ 2) := by ring
    rw [e]
    nlinarith
  · intro s hs h1
    rw [← Real.exp_mul]
    set y := (s ^ 2)⁻¹ with hy
    have hys : y * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    have hy0 : 0 ≤ y := by positivity
    have ha := Real.add_one_le_exp (y * (1 / 3))
    have hE : 0 < Real.exp (y * (1 / 3)) := Real.exp_pos _
    rw [show -y * (1 / 3) = -(y * (1 / 3)) by ring, Real.exp_neg]
    have hkey : 1 ≤ 2 * s * (1 + y * (1 / 3)) := by
      nlinarith [sq_nonneg (s - 1 / 4), mul_pos hs hs]
    calc (Real.exp (y * (1 / 3)))⁻¹ ≤ (1 + y * (1 / 3))⁻¹ :=
          inv_anti₀ (by positivity) (by linarith)
      _ ≤ 2 * s := by
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          linarith
  · intro C ε hε
    set K := 2 * |C| + 1 with hK
    have hKpos : 0 < K := by positivity
    refine ⟨min 1 ((ε / K) ^ 2), by positivity, ?_⟩
    intro s hs hs0
    have h1 : s ≤ 1 := le_trans hs0 (min_le_left _ _)
    have h2 : s ≤ (ε / K) ^ 2 := le_trans hs0 (min_le_right _ _)
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    push_cast
    have h3 := limRate_mul_log_sq_le hs h1
    have hsq : (s * Real.log s) ^ 2 ≤ (ε / K) ^ 2 := by
      calc (s * Real.log s) ^ 2 = s * (s * Real.log s ^ 2) := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left h3 hs.le
        _ ≤ (ε / K) ^ 2 := by linarith
    have habs : |s * Real.log s| ≤ ε / K := abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
    have hb : -2 * C * (s * Real.log s) ≤ ε := by
      calc -2 * C * (s * Real.log s) ≤ |-2 * C * (s * Real.log s)| := le_abs_self _
        _ = 2 * |C| * |s * Real.log s| := by
            rw [abs_mul, abs_mul, abs_neg, abs_two]
        _ ≤ 2 * |C| * (ε / K) := mul_le_mul_of_nonneg_left habs (by positivity)
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ hKpos, hK]
            nlinarith [abs_nonneg C]
    calc C * -(2 * Real.log s) * s ^ 2 = s * (-2 * C * (s * Real.log s)) := by ring
      _ ≤ s * ε := mul_le_mul_of_nonneg_left hb hs.le
      _ = ε * s := mul_comm _ _

end GlobalTheory.CompanionTheory.Ar.PB
