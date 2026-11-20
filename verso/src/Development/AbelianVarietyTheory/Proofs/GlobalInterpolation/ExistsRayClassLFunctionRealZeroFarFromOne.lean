import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowthStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacterStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

/- English proof (translation)
Take `⟨han, -, hbd, -⟩` from `GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ`. Establish `hB : 0 < 𝓕.B` using `by linarith [𝓕.B_ge]`. Establish `key : ∀ w ∈ Metric.closedBall z (1 / 10), 13 / 20 ≤ w.re ∧ ‖w‖ ≤ 27 / 20`. Introduce `w hw`. Rewrite `hz`, `hw` using `[Metric.mem_closedBall, dist_eq_norm]`.

Establish `h1 : ‖w - 1‖ ≤ 7 / 20`. Establish `: w - 1 = (w - z) + (z - 1)` using `by ring`. Rewrite using `[this]`. Combine the linear relations using `[norm_add_le (w - z) (z - 1)]`. Prove the components needed by the constructor for the conclusion.

Establish `h2` using `Complex.abs_re_le_norm (w - 1)`. Establish `h3` using `(abs_le.1 (h2.trans h1)).1`. Simplify using `only [sub_re, one_re] at h3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: w = (w - 1) + 1` using `by ring`.

Rewrite using `[this]`. Establish `h2` using `norm_add_le (w - 1) 1`. Rewrite `h2` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : DiffContOnCl ℂ (𝓕.F χ) (Metric.ball z (1 / 10))`.

Apply `DifferentiableOn.diffContOnCl` to reduce the goal to its premises. Rewrite using `[closure_ball z (by norm_num)]`. Introduce `w hw`. Use `(key w hw).1` as an intermediate fact. Conclude with `(han w (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt.differentiableWithinAt`.

Establish `h` using `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (C := 1800 * 𝓕.B) (by norm_num : (0 : ℝ) < 1 / 10) hd (by`. Introduce `w hw`. Take `⟨h1, h2⟩` from `key w (Metric.sphere_subset_closedBall hw)`. Establish `h3` using `hbd w (by linarith)`. Establish `h4 : (‖w‖ + 1) ^ 2 ≤ 6` using `by nlinarith [norm_nonneg w]`.

Use the proof step `nlinarith)`. Combine the linear relations using `[show 1800 * 𝓕.B / (1 / 10) = 18000 * 𝓕.B by ring]`.
-/
theorem LFam.norm_deriv_F_le_near_one (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (z : ℂ)
    (hz : z ∈ Metric.closedBall (1 : ℂ) (1 / 4)) : ‖deriv (𝓕.F χ) z‖ ≤ 18000 * 𝓕.B := by
  obtain ⟨han, -, hbd, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  have hB : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have key : ∀ w ∈ Metric.closedBall z (1 / 10), 13 / 20 ≤ w.re ∧ ‖w‖ ≤ 27 / 20 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hz hw
    have h1 : ‖w - 1‖ ≤ 7 / 20 := by
      have : w - 1 = (w - z) + (z - 1) := by ring
      rw [this]
      linarith [norm_add_le (w - z) (z - 1)]
    constructor
    · have h2 := Complex.abs_re_le_norm (w - 1)
      have h3 := (abs_le.1 (h2.trans h1)).1
      simp only [sub_re, one_re] at h3
      linarith
    · have : w = (w - 1) + 1 := by ring
      rw [this]
      have h2 := norm_add_le (w - 1) 1
      rw [norm_one] at h2
      linarith
  have hd : DiffContOnCl ℂ (𝓕.F χ) (Metric.ball z (1 / 10)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num)]
    intro w hw
    have := (key w hw).1
    exact (han w (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt.differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (C := 1800 * 𝓕.B) (by norm_num : (0 : ℝ) < 1 / 10) hd
    (by
      intro w hw
      obtain ⟨h1, h2⟩ := key w (Metric.sphere_subset_closedBall hw)
      have h3 := hbd w (by linarith)
      have h4 : (‖w‖ + 1) ^ 2 ≤ 6 := by nlinarith [norm_nonneg w]
      nlinarith)
  linarith [show 1800 * 𝓕.B / (1 / 10) = 18000 * 𝓕.B by ring]

/- English proof (translation)
Take `⟨A, c, hA, hc, h⟩` from `GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character`. Use `⟨A + 1, c / 18000, by linarith, by positivity, ?_⟩` and prove the remaining obligations. Introduce `𝓕 χ β hχ hβ h0`. Establish `hB : 0 < 𝓕.B` using `by linarith [𝓕.B_ge]`. Establish `hβ1 : β ≤ 1`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `(GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ β (by simpa using hlt)).2.2.1 h0`. Take `⟨han, -, -, -⟩` from `GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ`. Establish `hn : ‖(1 : ℂ) - β‖ = 1 - β`.

Rewrite using `[show (1 : ℂ) - β = ((1 - β : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]`. Establish `hmv` using `(convex_closedBall (1 : ℂ) (1 / 4)).norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := 𝓕.F χ) (C := 18000 * 𝓕.B) (x := (β : ℂ)) (y := 1) (by`. Introduce `z hz`. Rewrite `hz` using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `h3` using `(abs_le.1 ((Complex.abs_re_le_norm (z - 1)).trans hz)).1`.

Simplify using `only [sub_re, one_re] at h3`. Conclude with `(han z (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt)`. Use the proof step `(fun z hz => 𝓕.norm_deriv_F_le_near_one χ z hz)`. Use the proof step `(by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, hn]; linarith)`. Use the proof step `(Metric.mem_closedBall_self (by norm_num))`.

Rewrite `hmv` using `[h0, sub_zero, hn]`. Establish `h1` using `(h 𝓕 χ hχ).trans hmv`. Establish `hp : 0 < 𝓕.B ^ A` using `Real.rpow_pos_of_pos hB A`. Rewrite using `[Real.rpow_add hB, Real.rpow_one, div_le_iff₀ (by positivity)]`. Rewrite `h1` using `[div_le_iff₀ hp]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem LFam.real_zero_far_from_one : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (β : ℝ), χ * χ = 1 → 3 / 4 ≤ β → 𝓕.F χ β = 0 → c / 𝓕.B ^ A ≤ 1 - β := by
  obtain ⟨A, c, hA, hc, h⟩ := GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character
  refine ⟨A + 1, c / 18000, by linarith, by positivity, ?_⟩
  intro 𝓕 χ β hχ hβ h0
  have hB : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have hβ1 : β ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ β (by simpa using hlt)).2.2.1 h0
  obtain ⟨han, -, -, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  have hn : ‖(1 : ℂ) - β‖ = 1 - β := by
    rw [show (1 : ℂ) - β = ((1 - β : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hmv := (convex_closedBall (1 : ℂ) (1 / 4)).norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := 𝓕.F χ)
    (C := 18000 * 𝓕.B) (x := (β : ℂ)) (y := 1)
    (by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h3 := (abs_le.1 ((Complex.abs_re_le_norm (z - 1)).trans hz)).1
      simp only [sub_re, one_re] at h3
      exact (han z (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt)
    (fun z hz => 𝓕.norm_deriv_F_le_near_one χ z hz)
    (by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, hn]; linarith)
    (Metric.mem_closedBall_self (by norm_num))
  rw [h0, sub_zero, hn] at hmv
  have h1 := (h 𝓕 χ hχ).trans hmv
  have hp : 0 < 𝓕.B ^ A := Real.rpow_pos_of_pos hB A
  rw [Real.rpow_add hB, Real.rpow_one, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hp] at h1
  nlinarith

end GlobalTheory.Hk
