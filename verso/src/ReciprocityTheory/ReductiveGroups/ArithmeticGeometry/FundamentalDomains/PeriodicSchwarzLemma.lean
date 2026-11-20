import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma

open Complex Filter Function Function.Periodic Metric Set
open scoped Topology Real

/- English proof (translation)
Establish `hM0 : (M : ℝ) ≠ 0` using `hM.ne'`. Establish `hT : 0 < T` using `ht.trans htT`. Use `set F := cuspFunction M g with hF`. Use `set R := Real.exp (2 * π * t / M) with hRdef`. Establish `hR : 0 < R` using `Real.exp_pos _`.

Establish `h1R : 1 < R`. Use `Real.exp_lt_exp.2 (show (0 : ℝ) < 2 * π * t / M by positivity)` as an intermediate fact. Rewrite `this` using `[Real.exp_zero]`. Rewrite using `[hRdef]`. Conclude with `this`.

Establish `hF0 : F 0 = 0` using `cuspFunction_zero_of_zero_at_inf hM hzero`. Establish `hdiffF : DifferentiableOn ℂ F (closedBall 0 R)`. Introduce `q hq`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Distinguish the cases in `hq0 : q = 0`.

Substitute `hq0` using the available equality. Establish `hev : ∀ᶠ z : ℂ in comap im atTop, 0 ≤ z.im` using `tendsto_comap.eventually (eventually_ge_atTop 0)`. Conclude with `differentiableAt_cuspFunction_zero hM hper (hev.mono fun z hz => hdiff z (by linarith)) (hzero.isBigO_one ℝ)`. Rewrite using `[← qParam_right_inv hM0 hq0]`. Apply `differentiableAt_cuspFunction hM0 hper` to reduce the goal to its premises.

Apply `hdiff` to reduce the goal to its premises. Establish `hqn : 0 < ‖q‖` using `norm_pos_iff.2 hq0`. Establish `hqR : ‖q‖ ≤ R` using `by simpa [mem_closedBall, dist_zero_right] using hq`. Establish `hlog : Real.log ‖q‖ ≤ 2 * π * t / M`. Combine the equalities or inequalities in the displayed calculation.

Establish `key : M / (2 * π) * Real.log ‖q‖ ≤ t`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[im_invQParam]`. Establish `: -M / (2 * π) * Real.log ‖q‖ = -(M / (2 * π) * Real.log ‖q‖)` using `by ring`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdsl : DifferentiableOn ℂ (dslope F 0) (closedBall 0 R)` using `(differentiableOn_dslope (closedBall_mem_nhds 0 hR)).2 hdiffF`. Establish `hdc : DiffContOnCl ℂ (dslope F 0) (ball 0 R)` using `hdsl.diffContOnCl_ball subset_rfl`. Establish `hfront : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖dslope F 0 z‖ ≤ B / R`. Introduce `z hz`.

Rewrite `hz` using `[frontier_ball 0 hR.ne', mem_sphere_zero_iff_norm]`. Establish `hz0 : z ≠ 0`. Introduce `h`. Rewrite `hz` using `[h, norm_zero]`. Conclude with `hR.ne' hz.symm`.

Rewrite using `[dslope_of_ne _ hz0, slope_def_field, hF0, sub_zero, sub_zero, norm_div, hz]`. Apply `div_le_div_of_nonneg_right _ hR.le` to reduce the goal to its premises. Rewrite using `[hF, cuspFunction_eq_of_nonzero _ _ hz0]`. Apply `hB` to reduce the goal to its premises. Rewrite using `[im_invQParam, hz, hRdef, Real.log_exp]`.

Clear the denominators using the available nonvanishing facts. Establish `h1 : (1 : ℂ) ∈ closure (ball (0 : ℂ) R)` using `subset_closure (by simpa [mem_ball, dist_zero_right] using h1R)`. Establish `hmain` using `norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfront h1`. Establish `hq1 : qParam M 0 = 1` using `by simp [qParam]`. Establish `hg0 : g 0 = dslope F 0 1`.

Rewrite using `[dslope_of_ne _ one_ne_zero, slope_def_field, hF0, sub_zero, sub_zero, div_one, ← hq1, hF, eq_cuspFunction hM0 hper]`. Rewrite using `[hg0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hRdef, show -2 * π * t / M = -(2 * π * t / M) by ring, Real.exp_neg, div_eq_mul_inv, mul_comm]`.
-/
theorem periodic_schwarz {g : ℂ → ℂ} {M T t B : ℝ} (hM : 0 < M) (ht : 0 < t) (htT : t < T)
    (hper : Periodic g M) (hdiff : ∀ z : ℂ, -T < z.im → DifferentiableAt ℂ g z)
    (hzero : Tendsto g (comap im atTop) (𝓝 0)) (hB : ∀ z : ℂ, z.im = -t → ‖g z‖ ≤ B) :
    ‖g 0‖ ≤ Real.exp (-2 * π * t / M) * B := by
  have hM0 : (M : ℝ) ≠ 0 := hM.ne'
  have hT : 0 < T := ht.trans htT
  set F := cuspFunction M g with hF
  set R := Real.exp (2 * π * t / M) with hRdef
  have hR : 0 < R := Real.exp_pos _
  have h1R : 1 < R := by
    have := Real.exp_lt_exp.2 (show (0 : ℝ) < 2 * π * t / M by positivity)
    rw [Real.exp_zero] at this
    rw [hRdef]
    exact this
  have hF0 : F 0 = 0 := cuspFunction_zero_of_zero_at_inf hM hzero
  have hdiffF : DifferentiableOn ℂ F (closedBall 0 R) := by
    intro q hq
    apply DifferentiableAt.differentiableWithinAt
    by_cases hq0 : q = 0
    · subst hq0
      have hev : ∀ᶠ z : ℂ in comap im atTop, 0 ≤ z.im :=
        tendsto_comap.eventually (eventually_ge_atTop 0)
      exact differentiableAt_cuspFunction_zero hM hper
        (hev.mono fun z hz => hdiff z (by linarith)) (hzero.isBigO_one ℝ)
    · rw [← qParam_right_inv hM0 hq0]
      apply differentiableAt_cuspFunction hM0 hper
      apply hdiff
      have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
      have hqR : ‖q‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hq
      have hlog : Real.log ‖q‖ ≤ 2 * π * t / M := by
        calc Real.log ‖q‖ ≤ Real.log R := Real.log_le_log hqn hqR
          _ = 2 * π * t / M := by rw [hRdef, Real.log_exp]
      have key : M / (2 * π) * Real.log ‖q‖ ≤ t := by
        calc M / (2 * π) * Real.log ‖q‖ ≤ M / (2 * π) * (2 * π * t / M) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = t := by field_simp
      rw [im_invQParam]
      have : -M / (2 * π) * Real.log ‖q‖ = -(M / (2 * π) * Real.log ‖q‖) := by ring
      rw [this]
      linarith
  have hdsl : DifferentiableOn ℂ (dslope F 0) (closedBall 0 R) :=
    (differentiableOn_dslope (closedBall_mem_nhds 0 hR)).2 hdiffF
  have hdc : DiffContOnCl ℂ (dslope F 0) (ball 0 R) :=
    hdsl.diffContOnCl_ball subset_rfl
  have hfront : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖dslope F 0 z‖ ≤ B / R := by
    intro z hz
    rw [frontier_ball 0 hR.ne', mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact hR.ne' hz.symm
    rw [dslope_of_ne _ hz0, slope_def_field, hF0, sub_zero, sub_zero, norm_div, hz]
    apply div_le_div_of_nonneg_right _ hR.le
    rw [hF, cuspFunction_eq_of_nonzero _ _ hz0]
    apply hB
    rw [im_invQParam, hz, hRdef, Real.log_exp]
    field_simp
  have h1 : (1 : ℂ) ∈ closure (ball (0 : ℂ) R) :=
    subset_closure (by simpa [mem_ball, dist_zero_right] using h1R)
  have hmain := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfront h1
  have hq1 : qParam M 0 = 1 := by simp [qParam]
  have hg0 : g 0 = dslope F 0 1 := by
    rw [dslope_of_ne _ one_ne_zero, slope_def_field, hF0, sub_zero, sub_zero, div_one,
      ← hq1, hF, eq_cuspFunction hM0 hper]
  rw [hg0]
  calc ‖dslope F 0 1‖ ≤ B / R := hmain
    _ = Real.exp (-2 * π * t / M) * B := by
      rw [hRdef, show -2 * π * t / M = -(2 * π * t / M) by ring, Real.exp_neg, div_eq_mul_inv,
        mul_comm]

end ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma
