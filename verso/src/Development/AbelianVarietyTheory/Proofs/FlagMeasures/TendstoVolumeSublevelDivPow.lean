import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2} = (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' Metric.closedBall 0 s`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]`. Rewrite using `[Real.sqrt_le_left hs]`. Rewrite using `[h1, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage measurableSet_closedBall.nullMeasurableSet, Measure.addHaar_closedBall _ _ hs]`.

Simplify using the standard rewrite rules.
-/
theorem volume_sum_sq_le_sq (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = ENNReal.ofReal (s ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h1 : {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' Metric.closedBall 0 s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff,
      EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_le_left hs]
  rw [h1, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, Measure.addHaar_closedBall _ _ hs]
  simp

/- English proof (translation)
Use `set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hV`. Establish `hVt : V ≠ ⊤` using `measure_ball_lt_top.ne`. Rewrite using `[tendsto_order]`. Prove the components needed by the constructor for the conclusion. Introduce `a ha`.

Establish `hcont : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * V) (nhds 1) (nhds V)`. Establish `h1 : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (nhds 1) (nhds 1)`. Establish `: Continuous (fun t : ℝ => ENNReal.ofReal (t ^ d))` using `ENNReal.continuous_ofReal.comp (continuous_pow d)`. Simplify using `using this.tendsto 1`. Simplify using `using ENNReal.Tendsto.mul_const h1 (Or.inr hVt)`.

Establish `hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), a < ENNReal.ofReal (t ^ d) * V ∧ 0 < t` using `nhdsWithin_le_nhds ((hcont.eventually (lt_mem_nhds ha)).and (lt_mem_nhds one_pos))`. Take `⟨t, ⟨hta, ht0⟩, ht1⟩` from `(hev.and self_mem_nhdsWithin).exists`. Establish `ht1 : t < 1` using `ht1`. Establish `hδ : 0 < 4 * (1 - t ^ 2)` using `by nlinarith`. Establish `hN : ∀ᶠ x in nhds (0 : Fin d → ℝ), N x < 4 * (1 - t ^ 2)` using `hc.eventually (gt_mem_nhds (by rw [h0]; exact hδ))`.

Take `⟨η, hη, hball⟩` from `Metric.eventually_nhds_iff.1 hN`. Establish `hr : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < η` using `nhdsWithin_le_nhds (gt_mem_nhds hη)`. Use `filter_upwards [hr, self_mem_nhdsWithin] with r hrη hr0`. Establish `hr0 : 0 < r` using `hr0`. Use `hta.trans_le ?_` and prove the remaining obligations.

Establish `hp : ENNReal.ofReal (r ^ d) ≠ 0`. Simplify using `using pow_pos hr0 d`. Rewrite using `[ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)]`. Establish `e : ENNReal.ofReal (t ^ d) * V * ENNReal.ofReal (r ^ d) = volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ (t * r) ^ 2}`. Rewrite using `[volume_sum_sq_le_sq d (by positivity), mul_pow, ENNReal.ofReal_mul (by positivity), ← hV]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `measure_mono fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Establish `htr : t * r < η` using `by nlinarith`.

Establish `hx' : dist x 0 < η`. Rewrite using `[dist_zero_right]`. Use `lt_of_le_of_lt ?_ htr` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Establish `: x i ^ 2 ≤ (t * r) ^ 2` using `(Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)).trans hx`.

Conclude with `abs_le_of_sq_le_sq this (by positivity)`. Establish `h1` using `hball hx'`. Establish `h2` using `hu x`. Establish `h3 : 0 ≤ N x` using `(Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hl x)`. Rewrite using `[Real.sqrt_le_left hr0.le]`.

Establish `h4 : t ^ 2 * N x ≤ t ^ 2 * r ^ 2`. Use `mul_le_mul_of_nonneg_left h1.le h3` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_mul_le_mul_left h4 (by positivity)`. Introduce `a ha filter_upwards [self_mem_nhdsWithin] with r hr0`.

Establish `hr0 : 0 < r` using `hr0`. Use `lt_of_le_of_lt ?_ ha` and prove the remaining obligations. Use `ENNReal.div_le_of_le_mul ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ← volume_sum_sq_le_sq d hr0.le]`. Use `measure_mono fun x hx => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Rewrite `hx` using `[Real.sqrt_le_left hr0.le]`. Conclude with `(hl x).trans hx`.
-/
theorem tendsto_volume_sublevel_div_pow (d : ℕ) (N : (Fin d → ℝ) → ℝ) (hc : ContinuousAt N 0)
    (h0 : N 0 = 0) (hl : ∀ x, ∑ i, x i ^ 2 ≤ N x) (hu : ∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) :
    Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} /
        ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hV
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * V) (nhds 1) (nhds V) := by
      have h1 : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (nhds 1) (nhds 1) := by
        have : Continuous (fun t : ℝ => ENNReal.ofReal (t ^ d)) :=
          ENNReal.continuous_ofReal.comp (continuous_pow d)
        simpa using this.tendsto 1
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hVt)
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), a < ENNReal.ofReal (t ^ d) * V ∧ 0 < t :=
      nhdsWithin_le_nhds ((hcont.eventually (lt_mem_nhds ha)).and (lt_mem_nhds one_pos))
    obtain ⟨t, ⟨hta, ht0⟩, ht1⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht1 : t < 1 := ht1
    have hδ : 0 < 4 * (1 - t ^ 2) := by nlinarith
    have hN : ∀ᶠ x in nhds (0 : Fin d → ℝ), N x < 4 * (1 - t ^ 2) :=
      hc.eventually (gt_mem_nhds (by rw [h0]; exact hδ))
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hN
    have hr : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < η :=
      nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hr, self_mem_nhdsWithin] with r hrη hr0
    have hr0 : 0 < r := hr0
    refine hta.trans_le ?_
    have hp : ENNReal.ofReal (r ^ d) ≠ 0 := by
      simpa using pow_pos hr0 d
    rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)]
    have e : ENNReal.ofReal (t ^ d) * V * ENNReal.ofReal (r ^ d)
        = volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ (t * r) ^ 2} := by
      rw [volume_sum_sq_le_sq d (by positivity), mul_pow,
        ENNReal.ofReal_mul (by positivity), ← hV]
      ring
    rw [e]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    have htr : t * r < η := by nlinarith
    have hx' : dist x 0 < η := by
      rw [dist_zero_right]
      refine lt_of_le_of_lt ?_ htr
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have : x i ^ 2 ≤ (t * r) ^ 2 :=
        (Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)).trans hx
      exact abs_le_of_sq_le_sq this (by positivity)
    have h1 := hball hx'
    have h2 := hu x
    have h3 : 0 ≤ N x := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hl x)
    rw [Real.sqrt_le_left hr0.le]
    have h4 : t ^ 2 * N x ≤ t ^ 2 * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1.le h3
      nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with r hr0
    have hr0 : 0 < r := hr0
    refine lt_of_le_of_lt ?_ ha
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm, ← volume_sum_sq_le_sq d hr0.le]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Real.sqrt_le_left hr0.le] at hx
    exact (hl x).trans hx

end GlobalTheory
