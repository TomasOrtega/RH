import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBrouwerFixedPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChangeOfVariablesDegree
set_option maxSynthPendingDepth 1

open scoped ContDiff
open Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hcont : ContinuousOn (fun x => ‖x - g x‖) (closedBall (0 : Fin n → ℝ) 2)` using `(continuous_id.sub hg.continuous).norm.continuousOn`. Take `⟨x₀, -, hmin⟩` from `(isCompact_closedBall (0 : Fin n → ℝ) 2).exists_isMinOn (nonempty_closedBall.2 zero_le_two) hcont`. Establish `hε : 0 < ‖x₀ - g x₀‖` using `norm_pos_iff.2 (sub_ne_zero.2 (hne x₀).symm)`.

Use `set δ := min ‖x₀ - g x₀‖ 1 with hδ_def`. Establish `hδ : 0 < δ` using `lt_min hε one_pos`. Set `χ : ContDiffBump (0 : Fin n → ℝ)` to `⟨2, 3, two_pos, by norm_num⟩`. Set `φ : (Fin n → ℝ) → Fin n → ℝ` to `fun x => x - χ x • g x`. Establish `hφ : ContDiff ℝ ∞ φ` using `contDiff_id.sub (χ.contDiff.smul hg)`.

Establish `hφc : HasCompactSupport (fun x => φ x - x)`. Establish `h : (fun x => φ x - x) = -((fun x => χ x) • g)`. Use function extensionality and compare the values at `x`. Simplify using `[φ]`. Rewrite using `[h]`.

Conclude with `χ.hasCompactSupport.smul_right.neg`. Establish `hφδ : ∀ x, δ ≤ ‖φ x‖`. Introduce `x`. Distinguish the cases in `hx : ‖x‖ ≤ 2`. Establish `hχ : χ x = 1` using `χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)`.

Establish `h2 : ‖x₀ - g x₀‖ ≤ ‖x - g x‖` using `isMinOn_iff.1 hmin x (mem_closedBall_zero_iff.2 hx)`. Simplify using `only [φ, hχ, one_smul]`. Conclude with `(min_le_left _ _).trans h2`. Use `push Not at hx`. Establish `h1 : ‖χ x • g x‖ ≤ 1`.

Rewrite using `[norm_smul, Real.norm_of_nonneg χ.nonneg]`. Conclude with `mul_le_one₀ χ.le_one (norm_nonneg _) (hgb x)`. Establish `h3 : ‖x‖ - ‖χ x • g x‖ ≤ ‖φ x‖` using `norm_sub_norm_le _ _`. Establish `h4 : δ ≤ 1` using `min_le_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `ψ : ContDiffBump (0 : Fin n → ℝ)` to `⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩`. Establish `hzero : ∀ x, ψ (φ x) = 0`. Introduce `x`. Assume the negation of the conclusion as `h`. Establish `hmem : φ x ∈ ball (0 : Fin n → ℝ) δ`.

Rewrite using `[← ψ.support_eq]`. Conclude with `h`. Rewrite `hmem` using `[mem_ball_zero_iff]`. Conclude with `absurd (hφδ x) (not_le.2 hmem)`. Establish `hL'` using `hL n φ hφ hφc ψ ψ.contDiff ψ.hasCompactSupport`.

Simplify using `only [hzero, zero_mul, MeasureTheory.integral_zero] at hL'`. Conclude with `(ψ.integral_pos (μ := MeasureTheory.volume)).ne hL'`.
-/
theorem BrouwerFixedPoint.smooth_of_changeOfVariablesDegree
    (hL : ChangeOfVariablesDegree.Statement) (n : ℕ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, ‖g x‖ ≤ 1) : ∃ x, g x = x := by
  by_contra hne
  push Not at hne
  have hcont : ContinuousOn (fun x => ‖x - g x‖) (closedBall (0 : Fin n → ℝ) 2) :=
    (continuous_id.sub hg.continuous).norm.continuousOn
  obtain ⟨x₀, -, hmin⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 2).exists_isMinOn
    (nonempty_closedBall.2 zero_le_two) hcont
  have hε : 0 < ‖x₀ - g x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀).symm)
  set δ := min ‖x₀ - g x₀‖ 1 with hδ_def
  have hδ : 0 < δ := lt_min hε one_pos

  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨2, 3, two_pos, by norm_num⟩
  let φ : (Fin n → ℝ) → Fin n → ℝ := fun x => x - χ x • g x
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.sub (χ.contDiff.smul hg)
  have hφc : HasCompactSupport (fun x => φ x - x) := by
    have h : (fun x => φ x - x) = -((fun x => χ x) • g) := by
      funext x; simp [φ]
    rw [h]
    exact χ.hasCompactSupport.smul_right.neg
  have hφδ : ∀ x, δ ≤ ‖φ x‖ := by
    intro x
    by_cases hx : ‖x‖ ≤ 2
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
      have h2 : ‖x₀ - g x₀‖ ≤ ‖x - g x‖ :=
        isMinOn_iff.1 hmin x (mem_closedBall_zero_iff.2 hx)
      simp only [φ, hχ, one_smul]
      exact (min_le_left _ _).trans h2
    · push Not at hx
      have h1 : ‖χ x • g x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
        exact mul_le_one₀ χ.le_one (norm_nonneg _) (hgb x)
      have h3 : ‖x‖ - ‖χ x • g x‖ ≤ ‖φ x‖ := norm_sub_norm_le _ _
      have h4 : δ ≤ 1 := min_le_right _ _
      linarith

  let ψ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hzero : ∀ x, ψ (φ x) = 0 := by
    intro x
    by_contra h
    have hmem : φ x ∈ ball (0 : Fin n → ℝ) δ := by
      rw [← ψ.support_eq]; exact h
    rw [mem_ball_zero_iff] at hmem
    exact absurd (hφδ x) (not_le.2 hmem)
  have hL' := hL n φ hφ hφc ψ ψ.contDiff ψ.hasCompactSupport
  simp only [hzero, zero_mul, MeasureTheory.integral_zero] at hL'
  exact (ψ.integral_pos (μ := MeasureTheory.volume)).ne hL'

/- English proof (translation)
Introduce `n f hf hmaps`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Use `set B := closedBall (0 : Fin n → ℝ) 1 with hB_def`. Establish `hB : IsCompact B` using `isCompact_closedBall _ _`.

Establish `hcont : ContinuousOn (fun x => ‖f x - x‖) B` using `(hf.sub continuousOn_id).norm`. Take `⟨x₀, hx₀, hmin⟩` from `hB.exists_isMinOn (nonempty_closedBall.2 zero_le_one) hcont`. Establish `hε : 0 < ‖f x₀ - x₀‖` using `norm_pos_iff.2 (sub_ne_zero.2 (hne x₀ hx₀))`. Set `P : (Fin n → ℝ) → Fin n → ℝ` to `fun x i => max (min (x i) 1) (-1)`. Establish `hPB : ∀ x, P x ∈ B`.

Introduce `x`. Rewrite using `[hB_def, mem_closedBall_zero_iff]`. Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_le]`. Conclude with `⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩`.

Establish `hPid : ∀ x ∈ B, P x = x`. Introduce `x hx`. Use function extensionality and compare the values at `i`. Establish `hi : |x i| ≤ 1`. Establish `h` using `(norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.1 hx)`.

Rewrite `h` using `[Real.norm_eq_abs]`. Then use the resulting hypothesis. Rewrite `hi` using `[abs_le]`. Simplify using `only [P, min_eq_left hi.2, max_eq_left hi.1]`. Establish `hPlip : ∀ x y, dist (P x) (P y) ≤ dist x y`. Introduce `x y`.

Use `(dist_pi_le_iff dist_nonneg).2 fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Set `F : (Fin n → ℝ) → Fin n → ℝ` to `fun x => f (P x)`. Establish `hFu : UniformContinuous F`. Establish `hfu : UniformContinuousOn f B` using `hB.uniformContinuousOn_of_continuous hf`.

Rewrite using `[Metric.uniformContinuous_iff]`. Introduce `η hη`. Take `⟨d, hd, hfd⟩` from `Metric.uniformContinuousOn_iff.1 hfu η hη`. Conclude with `⟨d, hd, fun {a b} hab => hfd _ (hPB a) _ (hPB b) ((hPlip a b).trans_lt hab)⟩`. Establish `hFB : ∀ x, ‖F x‖ ≤ 1` using `fun x => mem_closedBall_zero_iff.1 (hmaps (hPB x))`.

Use `set a := ‖f x₀ - x₀‖ / 3 with ha_def`. Establish `ha : 0 < a` using `by positivity`. Take `⟨G, hG, hGF⟩` from `hFu.exists_contDiff_dist_le ha`. Use `set c := (1 + a)⁻¹ with hc_def`. Establish `hc : c * (1 + a) = 1` using `inv_mul_cancel₀ (by positivity)`.

Establish `hc0 : 0 < c` using `by positivity`. Establish `hc1 : c ≤ 1` using `inv_le_one_of_one_le₀ (by linarith)`. Establish `hGb : ∀ x, ‖G x‖ ≤ 1 + a`. Introduce `x`. Establish `h1 : ‖G x‖ ≤ ‖F x‖ + ‖G x - F x‖` using `norm_le_norm_add_norm_sub' _ _`.

Establish `h2 : ‖G x - F x‖ < a` using `by rw [← dist_eq_norm]; exact hGF x`. Combine the linear relations using `[hFB x]`. Establish `hgb : ∀ x, ‖c • G x‖ ≤ 1`. Introduce `x`. Rewrite using `[norm_smul, Real.norm_of_nonneg hc0.le]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨x, hx⟩` from `BrouwerFixedPoint.smooth_of_changeOfVariablesDegree hL n (fun x => c • G x) (hG.const_smul c) hgb`. Establish `hx' : c • G x = x` using `hx`. Establish `hxB : x ∈ B`. Rewrite using `[hB_def, mem_closedBall_zero_iff, ← hx']`.

Conclude with `hgb x`. Establish `hFx : F x = f x` using `by simp only [F, hPid x hxB]`. Establish `h1 : ‖f x - G x‖ < a`. Rewrite using `[← hFx, ← dist_eq_norm, dist_comm]`. Conclude with `hGF x`.

Establish `h2 : ‖G x - x‖ ≤ a`. Establish `h : G x - x = (1 - c) • G x`. Rewrite using `[sub_smul, one_smul, hx']`. Rewrite using `[h, norm_smul, Real.norm_of_nonneg (by linarith)]`. Use `hGb x` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : ‖f x - x‖ ≤ ‖f x - G x‖ + ‖G x - x‖` using `norm_sub_le_norm_sub_add_norm_sub _ _ _`. Establish `h4 : ‖f x₀ - x₀‖ ≤ ‖f x - x‖` using `isMinOn_iff.1 hmin x hxB`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem BrouwerFixedPoint.proof (hL : ChangeOfVariablesDegree.Statement) :
    BrouwerFixedPoint.Statement := by
  intro n f hf hmaps
  by_contra hne
  push Not at hne
  set B := closedBall (0 : Fin n → ℝ) 1 with hB_def
  have hB : IsCompact B := isCompact_closedBall _ _
  have hcont : ContinuousOn (fun x => ‖f x - x‖) B := (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hB.exists_isMinOn (nonempty_closedBall.2 zero_le_one) hcont
  have hε : 0 < ‖f x₀ - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀ hx₀))

  let P : (Fin n → ℝ) → Fin n → ℝ := fun x i => max (min (x i) 1) (-1)
  have hPB : ∀ x, P x ∈ B := by
    intro x
    rw [hB_def, mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩
  have hPid : ∀ x ∈ B, P x = x := by
    intro x hx
    funext i
    have hi : |x i| ≤ 1 := by
      have h := (norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.1 hx)
      rwa [Real.norm_eq_abs] at h
    rw [abs_le] at hi
    simp only [P, min_eq_left hi.2, max_eq_left hi.1]
  have hPlip : ∀ x y, dist (P x) (P y) ≤ dist x y := by
    intro x y
    refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
    calc dist (P x i) (P y i) = |max (min (x i) 1) (-1) - max (min (y i) 1) (-1)| :=
          Real.dist_eq _ _
      _ ≤ |min (x i) 1 - min (y i) 1| := abs_max_sub_max_le_abs _ _ _
      _ ≤ max |x i - y i| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = dist (x i) (y i) := by simp [Real.dist_eq]
      _ ≤ dist x y := dist_le_pi_dist x y i

  let F : (Fin n → ℝ) → Fin n → ℝ := fun x => f (P x)
  have hFu : UniformContinuous F := by
    have hfu : UniformContinuousOn f B := hB.uniformContinuousOn_of_continuous hf
    rw [Metric.uniformContinuous_iff]
    intro η hη
    obtain ⟨d, hd, hfd⟩ := Metric.uniformContinuousOn_iff.1 hfu η hη
    exact ⟨d, hd, fun {a b} hab => hfd _ (hPB a) _ (hPB b) ((hPlip a b).trans_lt hab)⟩
  have hFB : ∀ x, ‖F x‖ ≤ 1 := fun x => mem_closedBall_zero_iff.1 (hmaps (hPB x))

  set a := ‖f x₀ - x₀‖ / 3 with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨G, hG, hGF⟩ := hFu.exists_contDiff_dist_le ha
  set c := (1 + a)⁻¹ with hc_def
  have hc : c * (1 + a) = 1 := inv_mul_cancel₀ (by positivity)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hGb : ∀ x, ‖G x‖ ≤ 1 + a := by
    intro x
    have h1 : ‖G x‖ ≤ ‖F x‖ + ‖G x - F x‖ := norm_le_norm_add_norm_sub' _ _
    have h2 : ‖G x - F x‖ < a := by rw [← dist_eq_norm]; exact hGF x
    linarith [hFB x]
  have hgb : ∀ x, ‖c • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hc0.le]
    calc c * ‖G x‖ ≤ c * (1 + a) := mul_le_mul_of_nonneg_left (hGb x) hc0.le
      _ = 1 := hc
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.smooth_of_changeOfVariablesDegree hL n (fun x => c • G x)
    (hG.const_smul c) hgb
  have hx' : c • G x = x := hx
  have hxB : x ∈ B := by
    rw [hB_def, mem_closedBall_zero_iff, ← hx']
    exact hgb x
  have hFx : F x = f x := by simp only [F, hPid x hxB]
  have h1 : ‖f x - G x‖ < a := by
    rw [← hFx, ← dist_eq_norm, dist_comm]; exact hGF x
  have h2 : ‖G x - x‖ ≤ a := by
    have h : G x - x = (1 - c) • G x := by
      rw [sub_smul, one_smul, hx']
    rw [h, norm_smul, Real.norm_of_nonneg (by linarith)]
    have := hGb x
    nlinarith
  have h3 : ‖f x - x‖ ≤ ‖f x - G x‖ + ‖G x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ‖f x₀ - x₀‖ ≤ ‖f x - x‖ := isMinOn_iff.1 hmin x hxB
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
