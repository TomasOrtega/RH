import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.AdelicQuotientData.SeparatedThetaSum

/- English proof (translation)
Use `letI : MeasurableSpace X := borel X`. Use `haveI : BorelSpace X := ⟨rfl⟩`. Break down `subsingleton_or_nontrivial X with hX | hX` into its components or cases. Use `⟨0, le_rfl, fun ρ hρ P h1 _ => ?_⟩` and prove the remaining obligations. Establish `hP : P = ∅` using `Finset.eq_empty_of_forall_notMem fun p hp => by`.

Use `h1 p hp` as an intermediate fact. Rewrite `this` using `[Subsingleton.elim p 0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hP]`. Use `set D := Module.finrank ℝ X with hD`.

Use `set N := D + 1 with hN`. Set `μ : Measure X` to `Measure.addHaar`. Use `set f : X → ℝ := fun x => ((1 + ‖x‖) ^ N)⁻¹ with hf`. Establish `hf0 : ∀ x, 0 ≤ f x` using `fun x => by simp only [hf]; positivity`. Establish `hfi : Integrable f μ`.

Use `integrable_one_add_norm (μ := μ) (r := (N : ℝ)) (by rw [hN]; push_cast; exact lt_add_one _)` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [hf]`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast]`. Use `set c := μ.real (Metric.ball (0 : X) 1) with hc'`.

Establish `hc : 0 < c` using `ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 one_pos)) measure_ball_lt_top.ne`. Use `set I := ∫ x, f x ∂μ with hI`. Establish `hI0 : 0 ≤ I` using `integral_nonneg hf0`. Use `⟨(3 / 2) ^ N * I * 2 ^ D / c, by positivity, fun ρ hρ P h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hball : ∀ p : X, μ.real (Metric.ball p (ρ / 2)) = (ρ / 2) ^ D * c`.

Introduce `p`. Simplify using `only [Measure.real, Measure.addHaar_ball μ p (by positivity : 0 ≤ ρ / 2), hc']`. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Establish `hloc : ∀ p ∈ P, f p * ((ρ / 2) ^ D * c) ≤ (3 / 2) ^ N * ∫ x in Metric.ball p (ρ / 2), f x ∂μ`. Introduce `p hp`.

Rewrite using `[← hball p, mul_comm, ← smul_eq_mul, ← setIntegral_const, ← integral_const_mul]`. Use `setIntegral_mono_on (integrableOn_const (measure_ball_lt_top.ne)) (hfi.integrableOn.const_mul _) measurableSet_ball fun x hx => ?_` and prove the remaining obligations. Establish `hx' : ‖x‖ ≤ ‖p‖ + ρ / 2`. Use `norm_le_norm_add_norm_sub' x p` as an intermediate fact. Rewrite `hx` using `[Metric.mem_ball, dist_eq_norm]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp'` using `h1 p hp`. Establish `hle : 1 + ‖x‖ ≤ 3 / 2 * (1 + ‖p‖)` using `by linarith`. Simplify using `only [hf]`. Establish `e : ((1 + ‖p‖) ^ N)⁻¹ = (3 / 2) ^ N * ((3 / 2 * (1 + ‖p‖)) ^ N)⁻¹`.

Rewrite using `[mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]`. Rewrite using `[e]`. Use `gcongr`. Establish `hdisj : Set.Pairwise (P : Set X) (Function.onFun Disjoint fun p => Metric.ball p (ρ / 2))`. Introduce `p hp q hq hpq`.

Conclude with `Metric.ball_disjoint_ball (by rw [dist_eq_norm]; linarith [h2 p hp q hq hpq])`. Establish `hsum : ∑ p ∈ P, ∫ x in Metric.ball p (ρ / 2), f x ∂μ ≤ I`. Rewrite using `[← integral_biUnion_finset P (fun p _ => measurableSet_ball) hdisj (fun p _ => hfi.integrableOn)]`. Conclude with `setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)`. Establish `hpos : 0 < (ρ / 2) ^ D * c` using `by positivity`.

Establish `key : (∑ p ∈ P, f p) * ((ρ / 2) ^ D * c) ≤ (3 / 2) ^ N * I`. Rewrite using `[Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ∑ p ∈ P, f p ≤ (3 / 2) ^ N * I / ((ρ / 2) ^ D * c)` using `(le_div_iff₀ hpos).2 key`. Use `h3.trans (le_of_eq ?_)` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_assoc, ← mul_pow, div_mul_cancel₀ ρ two_ne_zero]`.
-/
theorem sep_sum (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∀ P : Finset X, (∀ p ∈ P, ρ ≤ ‖p‖) →
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ ≤ ‖p - q‖) →
      ∑ p ∈ P, ((1 + ‖p‖) ^ (Module.finrank ℝ X + 1))⁻¹ ≤ C * (ρ ^ Module.finrank ℝ X)⁻¹ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  rcases subsingleton_or_nontrivial X with hX | hX
  · refine ⟨0, le_rfl, fun ρ hρ P h1 _ => ?_⟩
    have hP : P = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      have := h1 p hp
      rw [Subsingleton.elim p 0, norm_zero] at this
      linarith
    simp [hP]
  set D := Module.finrank ℝ X with hD
  set N := D + 1 with hN
  let μ : Measure X := Measure.addHaar
  set f : X → ℝ := fun x => ((1 + ‖x‖) ^ N)⁻¹ with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hfi : Integrable f μ := by
    have := integrable_one_add_norm (μ := μ) (r := (N : ℝ)) (by rw [hN]; push_cast; exact lt_add_one _)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  set c := μ.real (Metric.ball (0 : X) 1) with hc'
  have hc : 0 < c := ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 one_pos)) measure_ball_lt_top.ne
  set I := ∫ x, f x ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg hf0
  refine ⟨(3 / 2) ^ N * I * 2 ^ D / c, by positivity, fun ρ hρ P h1 h2 => ?_⟩
  have hball : ∀ p : X, μ.real (Metric.ball p (ρ / 2)) = (ρ / 2) ^ D * c := by
    intro p
    simp only [Measure.real, Measure.addHaar_ball μ p (by positivity : 0 ≤ ρ / 2), hc']
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hloc : ∀ p ∈ P, f p * ((ρ / 2) ^ D * c) ≤ (3 / 2) ^ N * ∫ x in Metric.ball p (ρ / 2), f x ∂μ := by
    intro p hp
    rw [← hball p, mul_comm, ← smul_eq_mul, ← setIntegral_const, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_const (measure_ball_lt_top.ne))
      (hfi.integrableOn.const_mul _) measurableSet_ball fun x hx => ?_
    have hx' : ‖x‖ ≤ ‖p‖ + ρ / 2 := by
      have := norm_le_norm_add_norm_sub' x p
      rw [Metric.mem_ball, dist_eq_norm] at hx
      linarith
    have hp' := h1 p hp
    have hle : 1 + ‖x‖ ≤ 3 / 2 * (1 + ‖p‖) := by linarith
    simp only [hf]
    have e : ((1 + ‖p‖) ^ N)⁻¹ = (3 / 2) ^ N * ((3 / 2 * (1 + ‖p‖)) ^ N)⁻¹ := by
      rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rw [e]
    gcongr
  have hdisj : Set.Pairwise (P : Set X) (Function.onFun Disjoint fun p => Metric.ball p (ρ / 2)) := by
    intro p hp q hq hpq
    exact Metric.ball_disjoint_ball (by rw [dist_eq_norm]; linarith [h2 p hp q hq hpq])
  have hsum : ∑ p ∈ P, ∫ x in Metric.ball p (ρ / 2), f x ∂μ ≤ I := by
    rw [← integral_biUnion_finset P (fun p _ => measurableSet_ball) hdisj (fun p _ => hfi.integrableOn)]
    exact setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)
  have hpos : 0 < (ρ / 2) ^ D * c := by positivity
  have key : (∑ p ∈ P, f p) * ((ρ / 2) ^ D * c) ≤ (3 / 2) ^ N * I := by
    rw [Finset.sum_mul]
    calc ∑ p ∈ P, f p * ((ρ / 2) ^ D * c) ≤ ∑ p ∈ P, (3 / 2) ^ N * ∫ x in Metric.ball p (ρ / 2), f x ∂μ :=
          Finset.sum_le_sum hloc
      _ = (3 / 2) ^ N * ∑ p ∈ P, ∫ x in Metric.ball p (ρ / 2), f x ∂μ := by rw [Finset.mul_sum]
      _ ≤ (3 / 2) ^ N * I := by gcongr
  have h3 : ∑ p ∈ P, f p ≤ (3 / 2) ^ N * I / ((ρ / 2) ^ D * c) := (le_div_iff₀ hpos).2 key
  refine h3.trans (le_of_eq ?_)
  field_simp
  rw [mul_assoc, ← mul_pow, div_mul_cancel₀ ρ two_ne_zero]

end PositivityTheory.AdelicQuotientData.SeparatedThetaSum

end
