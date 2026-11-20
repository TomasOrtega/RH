import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `n g ρ b hρ hb hg hI`. Use `set I := ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) with hIdef`. Use `set v := volume (Metric.ball (0 : V n) 1) with hv`. Establish `hv0 : v ≠ 0` using `(Metric.measure_ball_pos volume _ one_pos).ne'`. Establish `hvt : v ≠ ⊤` using `measure_ball_lt_top.ne`.

Establish `hvr : 0 < v.toReal` using `ENNReal.toReal_pos hv0 hvt`. Establish `hdim : Module.finrank ℝ (V n) = 2 * n`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`. Use `set K : ℝ := (4 : ℝ) ^ b * 16 ^ n * I.toReal / v.toReal with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`.

Use `⟨Real.sqrt K, ρ / 2, by positivity, fun z hz hzρ => ?_⟩` and prove the remaining obligations. Use `set t := ‖z‖ with ht`. Establish `ht0 : 0 < t` using `norm_pos_iff.2 hz`. Establish `hsub : Metric.ball z (t / 2) ⊆ Metric.ball (0 : V n) ρ`. Apply `Metric.ball_subset_ball'` to reduce the goal to its premises.

Rewrite using `[dist_zero_right]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmv` using `ReciprocityTheory.L2DbarEstimates.C.mv n z (t / 2) g (fun _ => 1) (hg.mono hsub) measurable_const`. Simplify using `only [mul_one, lintegral_const, Measure.restrict_apply_univ, one_mul] at hmv`. Rewrite `hmv` using `[Measure.addHaar_ball_of_pos volume z (half_pos ht0), hdim, ← hv]`.

Establish `hs : 0 ≤ b + (n : ℝ)` using `by positivity`. Establish `hbound : ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2 ≤ ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * I`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' Metric.isOpen_ball.measurableSet fun w hw => ?_` and prove the remaining obligations. Establish `hw' : ‖w - z‖ < t / 2` using `by rwa [Metric.mem_ball, dist_eq_norm] at hw`.

Establish `h1 : ‖w‖ ≤ 2 * t`. Use `norm_sub_norm_le w z` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 0 < ‖w‖`. Use `norm_sub_norm_le z w` as an intermediate fact.

Rewrite `this` using `[norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `h3 : (‖w‖ ^ 2) ^ (b + (n : ℝ)) ≤ ((2 * t) ^ 2) ^ (b + (n : ℝ))` using `Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ h2.le h1 2) hs`.

Establish `h4 : 0 < (‖w‖ ^ 2) ^ (b + (n : ℝ))` using `by positivity`. Rewrite using `[Real.rpow_neg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * ∫⁻ w in Metric.ball z (t / 2), ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ ≤ _ := by gcongr`.

Conclude with `lintegral_mono_set hsub`. Establish `hfin` using `hmv.trans hbound`. Establish `hr` using `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hfin`. Rewrite `hr` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]`. Establish `hid : ((2 * t) ^ 2) ^ (b + (n : ℝ)) = (4 : ℝ) ^ b * (t ^ b) ^ 2 * (16 ^ n * (t / 2) ^ (2 * n))`.

Rewrite using `[Real.rpow_add (by positivity), Real.rpow_natCast]`. Use `congr 1`. Rewrite using `[show (2 * t) ^ 2 = 4 * (t * t) by ring, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ht0.le ht0.le, sq]`. Rewrite using `[pow_mul, ← mul_pow]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hr` using `[hid]`. Establish `hp : 0 < (t / 2) ^ (2 * n)` using `by positivity`. Establish `hsq : ‖g z‖ ^ 2 ≤ K * (t ^ b) ^ 2`. Establish `hc : 0 < (t / 2) ^ (2 * n) * v.toReal` using `by positivity`.

Use `le_of_mul_le_mul_right (hr.trans (le_of_eq ?_)) hc` and prove the remaining obligations. Rewrite using `[hK]`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul hK0, Real.sqrt_sq (by positivity)]`.
-/
theorem norm_le_rpow_of_weighted_sq_integrable :
    ∀ (n : ℕ) (g : V n → ℂ) (ρ b : ℝ), 0 < ρ → 0 ≤ b → DifferentiableOn ℂ g (Metric.ball 0 ρ) →
      ∫⁻ z in Metric.ball (0 : V n) ρ,
        ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) < ⊤ →
      ∃ C ε : ℝ, 0 < ε ∧ ∀ z : V n, z ≠ 0 → ‖z‖ < ε → ‖g z‖ ≤ C * ‖z‖ ^ b := by
  intro n g ρ b hρ hb hg hI
  set I := ∫⁻ z in Metric.ball (0 : V n) ρ,
        ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) with hIdef
  set v := volume (Metric.ball (0 : V n) 1) with hv
  have hv0 : v ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hvt : v ≠ ⊤ := measure_ball_lt_top.ne
  have hvr : 0 < v.toReal := ENNReal.toReal_pos hv0 hvt
  have hdim : Module.finrank ℝ (V n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  set K : ℝ := (4 : ℝ) ^ b * 16 ^ n * I.toReal / v.toReal with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨Real.sqrt K, ρ / 2, by positivity, fun z hz hzρ => ?_⟩
  set t := ‖z‖ with ht
  have ht0 : 0 < t := norm_pos_iff.2 hz
  have hsub : Metric.ball z (t / 2) ⊆ Metric.ball (0 : V n) ρ := by
    apply Metric.ball_subset_ball'
    rw [dist_zero_right]; linarith
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv n z (t / 2) g (fun _ => 1) (hg.mono hsub) measurable_const
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, one_mul] at hmv
  rw [Measure.addHaar_ball_of_pos volume z (half_pos ht0), hdim, ← hv] at hmv
  have hs : 0 ≤ b + (n : ℝ) := by positivity
  have hbound : ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2 ≤
      ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * I := by
    calc ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2
        ≤ ∫⁻ w in Metric.ball z (t / 2), ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) *
            ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) := by
          refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun w hw => ?_
          have hw' : ‖w - z‖ < t / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
          have h1 : ‖w‖ ≤ 2 * t := by
            have := norm_sub_norm_le w z
            linarith
          have h2 : 0 < ‖w‖ := by
            have := norm_sub_norm_le z w
            rw [norm_sub_rev] at this
            linarith
          rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          have h3 : (‖w‖ ^ 2) ^ (b + (n : ℝ)) ≤ ((2 * t) ^ 2) ^ (b + (n : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ h2.le h1 2) hs
          have h4 : 0 < (‖w‖ ^ 2) ^ (b + (n : ℝ)) := by positivity
          rw [Real.rpow_neg (by positivity)]
          calc ‖g w‖ ^ 2 = (‖w‖ ^ 2) ^ (b + (n : ℝ)) *
                (‖g w‖ ^ 2 * ((‖w‖ ^ 2) ^ (b + (n : ℝ)))⁻¹) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * ∫⁻ w in Metric.ball z (t / 2),
            ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact lintegral_mono_set hsub
  have hfin := hmv.trans hbound
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_enorm, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hr
  have hid : ((2 * t) ^ 2) ^ (b + (n : ℝ)) =
      (4 : ℝ) ^ b * (t ^ b) ^ 2 * (16 ^ n * (t / 2) ^ (2 * n)) := by
    rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    congr 1
    · rw [show (2 * t) ^ 2 = 4 * (t * t) by ring, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow ht0.le ht0.le, sq]
    · rw [pow_mul, ← mul_pow]
      congr 1
      ring
  rw [hid] at hr
  have hp : 0 < (t / 2) ^ (2 * n) := by positivity
  have hsq : ‖g z‖ ^ 2 ≤ K * (t ^ b) ^ 2 := by
    have hc : 0 < (t / 2) ^ (2 * n) * v.toReal := by positivity
    refine le_of_mul_le_mul_right (hr.trans (le_of_eq ?_)) hc
    rw [hK]
    field_simp
  calc ‖g z‖ ≤ Real.sqrt (K * (t ^ b) ^ 2) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt K * t ^ b := by
      rw [Real.sqrt_mul hK0, Real.sqrt_sq (by positivity)]

end GlobalTheory
