import Mathlib

namespace GlobalTheory.CompanionTheory.Strip

/- English proof (translation)
Use `set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS`. Establish `hpi : 0 < Real.pi / 4` using `by positivity`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h : S = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4}`. Use extensionality with `z`.

Simplify using `[hS]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const`. Introduce `t`. Simplify using `[hS, hpi]`.

Introduce `z hz`. Establish `hopen : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4}`. Establish `h : {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} = ⋂ j, {r : ℝ | r * |X j| < Real.pi / 4}`. Use extensionality with `r`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const`. Establish `hmem : |z.im| ∈ {r : ℝ | ∀ j, r * |X j| < Real.pi / 4}`. Introduce `j`. Establish `h` using `hz j`.

Rewrite `h` using `[abs_mul]`. Then use the resulting hypothesis. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hopen _ hmem`. Use `⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, Complex.dist_eq]`. Establish `h : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I`.

Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `w hw j`. Rewrite `hw` using `[Metric.mem_ball, Complex.dist_eq]`.

Establish `him : |w.im| < |z.im| + ε / 2`. Establish `h1 : |(w - (z.re : ℂ)).im| ≤ ‖w - (z.re : ℂ)‖` using `Complex.abs_im_le_norm _`. Simplify using `only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρ : (|z.im| + ε / 2) * |X j| < Real.pi / 4`.

Establish `hin : |z.im| + ε / 2 ∈ Metric.ball |z.im| ε`. Rewrite using `[Metric.mem_ball, Real.dist_eq, show |z.im| + ε / 2 - |z.im| = ε / 2 by ring, abs_of_pos (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hball hin j`. Use `show |w.im * X j| < Real.pi / 4`.

Rewrite using `[abs_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  have hpi : 0 < Real.pi / 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h : S = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by
      ext z
      simp [hS]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · intro t
    simp [hS, hpi]
  · intro z hz
    have hopen : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      have h : {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} = ⋂ j, {r : ℝ | r * |X j| < Real.pi / 4} := by
        ext r
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hmem : |z.im| ∈ {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      intro j
      have h := hz j
      rwa [abs_mul] at h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
    · intro w hw j
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h1 : |(w - (z.re : ℂ)).im| ≤ ‖w - (z.re : ℂ)‖ := Complex.abs_im_le_norm _
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
        linarith
      have hρ : (|z.im| + ε / 2) * |X j| < Real.pi / 4 := by
        have hin : |z.im| + ε / 2 ∈ Metric.ball |z.im| ε := by
          rw [Metric.mem_ball, Real.dist_eq, show |z.im| + ε / 2 - |z.im| = ε / 2 by ring,
            abs_of_pos (by positivity)]
          linarith
        exact hball hin j
      show |w.im * X j| < Real.pi / 4
      rw [abs_mul]
      calc |w.im| * |X j| ≤ (|z.im| + ε / 2) * |X j| :=
            mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ

end GlobalTheory.CompanionTheory.Strip
