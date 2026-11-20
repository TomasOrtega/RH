import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace ReciprocityTheory.MultiplicativeHeights

open Metric
open scoped InnerProductSpace

/- English proof (translation)
Introduce `V _ _ _ θ Λ ρ n hθ hne hper hcov hn`. Use `set f : V → ℝ := fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hf`. Establish `hfc : Continuous f`. Use `hθ.continuous` as an intermediate fact. Use `fun_prop`.

Establish `hρ : 0 ≤ ρ`. Take `⟨l, -, hl⟩` from `hcov 0`. Conclude with `(norm_nonneg _).trans hl`. Take `⟨z₀, -, hz₀⟩` from `(isCompact_closedBall (0 : V) ρ).exists_isMaxOn ⟨0, mem_closedBall_self hρ⟩ hfc.continuousOn`. Establish `hmax : ∀ v, f v ≤ f z₀`.

Introduce `v`. Take `⟨l, hl, hvl⟩` from `hcov v`. Establish `h1 : f (v - l) ≤ f z₀` using `hz₀ (by simpa [mem_closedBall, dist_zero_right] using hvl)`. Establish `h2 : f v = f (v - l)`. Use `hper l hl (v - l)` as an intermediate fact.

Simplify `this` using `[hf]`. Rewrite using `[h2]`. Conclude with `h1`. Use `set M := f z₀ with hM`. Establish `hMpos : 0 < M`.

Take `⟨z, hz⟩` from `hne`. Establish `: 0 < f z` using `mul_pos (norm_pos_iff.mpr hz) (Real.exp_pos _)`. Conclude with `this.trans_le (hmax z)`. Use `set h : V → ℂ := fun w => θ (z₀ + w) * Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z₀ w - ((Real.pi / 2 * ‖z₀‖ ^ 2 : ℝ) : ℂ)) with hh`. Establish `hdiff : Differentiable ℂ h`.

Establish `h1 : Differentiable ℂ fun w : V => θ (z₀ + w)` using `hθ.comp (differentiable_const _ |>.add differentiable_id)`. Establish `h2 : Differentiable ℂ fun w : V => innerSL ℂ z₀ w` using `(innerSL ℂ z₀).differentiable`. Conclude with `h1.mul ((h2.const_mul _ |>.sub_const _).cexp)`. Establish `hnorm : ∀ w, ‖h w‖ = f (z₀ + w) * Real.exp (Real.pi / 2 * ‖w‖ ^ 2)`. Introduce `w`.

Simplify using `only [hh, hf, norm_mul, Complex.norm_exp]`. Rewrite using `[norm_add_sq (𝕜 := ℂ), mul_assoc, ← Real.exp_add]`. Use `congr 1`. Rewrite using `[Complex.sub_re, Complex.ofReal_re]`. Simplify using `[innerSL_apply_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hexp : ∀ w : V, ‖w‖ < 3 / 5 → Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ 2`. Introduce `w hw`. Establish `hw2 : ‖w‖ ^ 2 ≤ (3 / 5) ^ 2`. Use `norm_nonneg w` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hpi` using `Real.pi_lt_d2`. Establish `hpi0` using `Real.pi_pos`. Establish `hlog` using `Real.log_two_gt_d9`. Establish `: Real.pi / 2 * ‖w‖ ^ 2 < Real.log 2` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `hbd : ∀ w ∈ ball (0 : V) (3 / 5), ‖h w‖ ≤ 2 * M`. Introduce `w hw`. Rewrite `hw` using `[mem_ball, dist_zero_right]`. Rewrite using `[hnorm w]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h0 : ‖h 0‖ = M` using `by rw [hnorm 0]; simp [hM]`. Establish `hsch` using `hS V (ball (0 : V) (3 / 5)) h (2 * M) isOpen_ball balanced_ball_zero hdiff.differentiableOn hbd`. Establish `hnpos : (0 : ℝ) < n` using `by linarith`. Take `⟨l, hl, hzl⟩` from `hcov ((n : ℂ) • z₀)`.

Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Use `set w : V := (n : ℂ)⁻¹ • l - z₀ with hw`. Establish `hnC : (n : ℂ) ≠ 0` using `by exact_mod_cast hnpos.ne'`. Establish `hwn : ‖w‖ ≤ ρ / n`. Establish `: w = (n : ℂ)⁻¹ • (l - (n : ℂ) • z₀)`.

Rewrite using `[hw, smul_sub, smul_smul, inv_mul_cancel₀ hnC, one_smul]`. Rewrite using `[this, norm_smul, norm_inv, Complex.norm_natCast, norm_sub_rev, le_div_iff₀ hnpos]`. Rewrite using `[inv_mul_eq_div, div_mul_cancel₀ _ hnpos.ne']`. Conclude with `hzl`. Establish `hw5 : ‖w‖ < 1 / 5`.

Use `hwn.trans_lt ?_` and prove the remaining obligations. Rewrite using `[div_lt_iff₀ hnpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwb : w ∈ ball (0 : V) (3 / 5)`. Rewrite using `[mem_ball, dist_zero_right]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `hsch w hwb`. Rewrite `key` using `[gauge_ball (by norm_num : (0 : ℝ) ≤ 3 / 5), h0]`. Establish `hhw : h w ≠ 0`. Introduce `hz`.

Rewrite `key` using `[hz, zero_sub, norm_neg, h0]`. Establish `: (2 * M + M) * (‖w‖ / (3 / 5)) < M`. Establish `: (2 * M + M) * (‖w‖ / (3 / 5)) = M * (5 * ‖w‖)` using `by ring`. Rewrite using `[this]`. Establish `: 5 * ‖w‖ < 1` using `by linarith`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzw : z₀ + w = (n : ℂ)⁻¹ • l` using `by rw [hw]; abel`. Use `left_ne_zero_of_mul hhw` as an intermediate fact. Rewrite `this` using `[hzw]`. Then use the resulting hypothesis.
-/
theorem torsionNonvanish_holds (hS : BalancedSchwarzStatement) : TorsionNonvanishStatement := by
  intro V _ _ _ θ Λ ρ n hθ hne hper hcov hn

  set f : V → ℝ := fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2) with hf
  have hfc : Continuous f := by
    have := hθ.continuous
    fun_prop
  have hρ : 0 ≤ ρ := by
    obtain ⟨l, -, hl⟩ := hcov 0
    exact (norm_nonneg _).trans hl

  obtain ⟨z₀, -, hz₀⟩ := (isCompact_closedBall (0 : V) ρ).exists_isMaxOn
    ⟨0, mem_closedBall_self hρ⟩ hfc.continuousOn
  have hmax : ∀ v, f v ≤ f z₀ := by
    intro v
    obtain ⟨l, hl, hvl⟩ := hcov v
    have h1 : f (v - l) ≤ f z₀ := hz₀ (by simpa [mem_closedBall, dist_zero_right] using hvl)
    have h2 : f v = f (v - l) := by
      have := hper l hl (v - l)
      simpa [hf] using this
    rw [h2]; exact h1
  set M := f z₀ with hM
  have hMpos : 0 < M := by
    obtain ⟨z, hz⟩ := hne
    have : 0 < f z := mul_pos (norm_pos_iff.mpr hz) (Real.exp_pos _)
    exact this.trans_le (hmax z)

  set h : V → ℂ := fun w => θ (z₀ + w) *
    Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z₀ w - ((Real.pi / 2 * ‖z₀‖ ^ 2 : ℝ) : ℂ)) with hh
  have hdiff : Differentiable ℂ h := by
    have h1 : Differentiable ℂ fun w : V => θ (z₀ + w) :=
      hθ.comp (differentiable_const _ |>.add differentiable_id)
    have h2 : Differentiable ℂ fun w : V => innerSL ℂ z₀ w := (innerSL ℂ z₀).differentiable
    exact h1.mul ((h2.const_mul _ |>.sub_const _).cexp)
  have hnorm : ∀ w, ‖h w‖ = f (z₀ + w) * Real.exp (Real.pi / 2 * ‖w‖ ^ 2) := by
    intro w
    simp only [hh, hf, norm_mul, Complex.norm_exp]
    rw [norm_add_sq (𝕜 := ℂ), mul_assoc, ← Real.exp_add]
    congr 1
    rw [Complex.sub_re, Complex.ofReal_re]
    simp [innerSL_apply_apply]
    ring

  have hexp : ∀ w : V, ‖w‖ < 3 / 5 → Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ 2 := by
    intro w hw
    have hw2 : ‖w‖ ^ 2 ≤ (3 / 5) ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hlog := Real.log_two_gt_d9
    have : Real.pi / 2 * ‖w‖ ^ 2 < Real.log 2 := by nlinarith
    calc Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr this.le
      _ = 2 := Real.exp_log (by norm_num)
  have hbd : ∀ w ∈ ball (0 : V) (3 / 5), ‖h w‖ ≤ 2 * M := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    rw [hnorm w]
    calc f (z₀ + w) * Real.exp (Real.pi / 2 * ‖w‖ ^ 2) ≤ M * 2 :=
          mul_le_mul (hmax _) (hexp w hw) (Real.exp_pos _).le hMpos.le
      _ = 2 * M := by ring
  have h0 : ‖h 0‖ = M := by rw [hnorm 0]; simp [hM]
  have hsch := hS V (ball (0 : V) (3 / 5)) h (2 * M) isOpen_ball balanced_ball_zero
    hdiff.differentiableOn hbd

  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨l, hl, hzl⟩ := hcov ((n : ℂ) • z₀)
  refine ⟨l, hl, ?_⟩
  set w : V := (n : ℂ)⁻¹ • l - z₀ with hw
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hwn : ‖w‖ ≤ ρ / n := by
    have : w = (n : ℂ)⁻¹ • (l - (n : ℂ) • z₀) := by
      rw [hw, smul_sub, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [this, norm_smul, norm_inv, Complex.norm_natCast, norm_sub_rev, le_div_iff₀ hnpos]
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hnpos.ne']
    exact hzl
  have hw5 : ‖w‖ < 1 / 5 := by
    refine hwn.trans_lt ?_
    rw [div_lt_iff₀ hnpos]; linarith
  have hwb : w ∈ ball (0 : V) (3 / 5) := by
    rw [mem_ball, dist_zero_right]; linarith
  have key := hsch w hwb
  rw [gauge_ball (by norm_num : (0 : ℝ) ≤ 3 / 5), h0] at key
  have hhw : h w ≠ 0 := by
    intro hz
    rw [hz, zero_sub, norm_neg, h0] at key
    have : (2 * M + M) * (‖w‖ / (3 / 5)) < M := by
      have : (2 * M + M) * (‖w‖ / (3 / 5)) = M * (5 * ‖w‖) := by ring
      rw [this]
      have : 5 * ‖w‖ < 1 := by linarith
      nlinarith
    linarith
  have hzw : z₀ + w = (n : ℂ)⁻¹ • l := by rw [hw]; abel
  have := left_ne_zero_of_mul hhw
  rwa [hzw] at this

end ReciprocityTheory.MultiplicativeHeights
