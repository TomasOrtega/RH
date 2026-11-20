import Mathlib

noncomputable section

open Metric

namespace PositivityTheory.Rg.Sw.SP

/- English proof (translation)
Establish `key : ∀ R : ℝ, 0 < R → R < ε → ‖iteratedDeriv j f 0‖ ≤ j.factorial * (C * R ^ r) / R ^ j`. Introduce `R hR hRε`. Use `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR ?_ ?_` and prove the remaining obligations. Conclude with `hf.diffContOnCl_ball (closedBall_subset_ball hRε)`. Introduce `z hz`.

Establish `hz' : z ∈ ball (0 : ℂ) ε`. Rewrite `hz` using `[mem_sphere_zero_iff_norm]`. Rewrite using `[mem_ball_zero_iff, hz]`. Conclude with `hRε`. Use `hb z hz'` as an intermediate fact.

Rewrite `this` using `[mem_sphere_zero_iff_norm.1 hz]`. Then use the resulting hypothesis. Establish `hlim : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * (C * R ^ r) / R ^ j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)`. Establish `e : ∀ R : ℝ, 0 < R → (j.factorial : ℝ) * (C * R ^ r) / R ^ j = j.factorial * C * R ^ (r - j)`. Introduce `R hR`. Establish `: R ^ r = R ^ (r - j) * R ^ j` using `by rw [← pow_add, Nat.sub_add_cancel hj.le]`.

Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Establish `h0 : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)`. Establish `: Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhds 0) (nhds ((j.factorial : ℝ) * C * 0 ^ (r - j)))` using `(continuous_const.mul (continuous_pow _)).tendsto 0`. Rewrite `this` using `[zero_pow (Nat.sub_ne_zero_of_lt hj), mul_zero]`.

Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `h0.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with R hR using (e R hR).symm`. Establish `hle : ‖iteratedDeriv j f 0‖ ≤ 0`. Use `ge_of_tendsto hlim ?_` and prove the remaining obligations.

Use `filter_upwards [Ioo_mem_nhdsGT hε] with R hR using key R hR.1 hR.2`. Conclude with `norm_le_zero_iff.1 hle`.
-/
theorem iteratedDeriv_zero_of_bound {f : ℂ → ℂ} {ε C : ℝ} {r : ℕ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (ball 0 ε)) (hb : ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖z‖ ^ r) {j : ℕ} (hj : j < r) :
    iteratedDeriv j f 0 = 0 := by
  have key : ∀ R : ℝ, 0 < R → R < ε → ‖iteratedDeriv j f 0‖ ≤ j.factorial * (C * R ^ r) / R ^ j := by
    intro R hR hRε
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR ?_ ?_
    · exact hf.diffContOnCl_ball (closedBall_subset_ball hRε)
    · intro z hz
      have hz' : z ∈ ball (0 : ℂ) ε := by
        rw [mem_sphere_zero_iff_norm] at hz
        rw [mem_ball_zero_iff, hz]; exact hRε
      have := hb z hz'
      rwa [mem_sphere_zero_iff_norm.1 hz] at this
  have hlim : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * (C * R ^ r) / R ^ j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have e : ∀ R : ℝ, 0 < R → (j.factorial : ℝ) * (C * R ^ r) / R ^ j = j.factorial * C * R ^ (r - j) := by
      intro R hR
      have : R ^ r = R ^ (r - j) * R ^ j := by rw [← pow_add, Nat.sub_add_cancel hj.le]
      rw [this]; field_simp
    have h0 : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhds 0) (nhds ((j.factorial : ℝ) * C * 0 ^ (r - j))) :=
        (continuous_const.mul (continuous_pow _)).tendsto 0
      rw [zero_pow (Nat.sub_ne_zero_of_lt hj), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with R hR using (e R hR).symm
  have hle : ‖iteratedDeriv j f 0‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with R hR using key R hR.1 hR.2
  exact norm_le_zero_iff.1 hle

/- English proof (translation)
Use `Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) 1) isBounded_ball hq.diffContOnCl (fun w hw => ?_) ?_` and prove the remaining obligations. Rewrite `hw` using `[frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm]`. Use `hM w hw` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_pow, hw, one_pow, one_mul]`. Then use the resulting hypothesis. Rewrite using `[closure_ball 0 one_ne_zero, mem_closedBall_zero_iff]`.

Conclude with `hz`.
-/
theorem norm_le_of_circle {q : ℂ → ℂ} (hq : Differentiable ℂ q) {r : ℕ} {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ r * q w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖q z‖ ≤ M := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) 1) isBounded_ball
    hq.diffContOnCl (fun w hw => ?_) ?_
  · rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hw
    have := hM w hw
    rwa [norm_mul, norm_pow, hw, one_pow, one_mul] at this
  · rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff]; exact hz

end PositivityTheory.Rg.Sw.SP
