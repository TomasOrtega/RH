import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StGrowthOffHypersurfacePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StEntirePolynomialGrowth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Simplify using `only [not_exists, not_and, not_not] at hall`. Take `⟨t, ht⟩` from `hne`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hV t ht`. Apply `hQ` to reduce the goal to its premises.

Use `MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)` and prove the remaining obligations. Conclude with `infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)`. Rewrite using `[map_zero]`. Apply `hall` to reduce the goal to its premises. Apply `hball` to reduce the goal to its premises.

Rewrite using `[ball_pi t hε]`. Conclude with `hx`.
-/
theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)
  · exact infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)
  · rw [map_zero]
    apply hall
    apply hball
    rw [ball_pi t hε]
    exact hx

/- English proof (translation)
Rewrite using `[dense_iff_inter_open]`. Introduce `V hV hne`. Take `⟨t, htV, ht⟩` from `exists_eval_ne_zero_of_isOpen hQ hV hne`. Conclude with `⟨t, htV, ht⟩`.
-/
theorem dense_eval_ne_zero {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨t, htV, ht⟩ := exists_eval_ne_zero_of_isOpen hQ hV hne
  exact ⟨t, htV, ht⟩

/- English proof (translation)
Introduce `d Q f C M hQ hf hb`. Establish `hg : Differentiable ℂ (fun y : Fin d → ℂ => eval y Q)` using `fun y => (AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)).differentiableAt`. Take `⟨F, hF, hFf⟩` from `IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof d Set.univ (fun y => eval y Q) f isOpen_univ hg.differentiableOn (fun V hV _ hne => exists_eval_ne_zero_of_isOpen hQ hV hne) (by simpa using hf) (fun τ _ => by`. Use `⟨Metric.ball τ 1, Metric.ball_mem_nhds τ one_pos, ?_⟩` and prove the remaining obligations. Use `isBounded_iff_forall_norm_le.2 ⟨|C| * (2 + ‖τ‖) ^ M, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, ⟨⟨hy, -⟩, hyQ⟩, rfl⟩`. Establish `hdist : ‖y‖ ≤ ‖τ‖ + 1`. Use `norm_le_norm_add_norm_sub' y τ` as an intermediate fact. Rewrite `hy` using `[Metric.mem_ball, dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `hFd : Differentiable ℂ F` using `differentiableOn_univ.1 hF`. Establish `hFc : Continuous F` using `hFd.continuous`. Establish `hclosed : IsClosed {y : Fin d → ℂ | ‖F y‖ ≤ C * (1 + ‖y‖) ^ M}` using `isClosed_le hFc.norm (continuous_const.mul ((continuous_const.add continuous_norm).pow M))`. Establish `hsub : {y : Fin d → ℂ | eval y Q ≠ 0} ⊆ {y | ‖F y‖ ≤ C * (1 + ‖y‖) ^ M}`.

Introduce `y hy`. Establish `: F y = f y` using `hFf ⟨Set.mem_univ y, hy⟩`. Use `show ‖F y‖ ≤ C * (1 + ‖y‖) ^ M`. Rewrite using `[this]`. Conclude with `hb y hy`.

Establish `hall : ∀ y, ‖F y‖ ≤ C * (1 + ‖y‖) ^ M`. Introduce `y`. Use `closure_minimal hsub hclosed` as an intermediate fact. Rewrite `this` using `[(dense_eval_ne_zero hQ).closure_eq]`. Conclude with `this (Set.mem_univ y)`.

Take `⟨p, hp⟩` from `h d F C M hFd hall`. Conclude with `⟨p, fun y hy => (hFf ⟨Set.mem_univ y, hy⟩).symm.trans (hp y)⟩`.
-/
theorem GrowthOffHypersurfacePolynomial.proof (h : EntirePolynomialGrowth.Statement) :
    GrowthOffHypersurfacePolynomial.Statement := by
  intro d Q f C M hQ hf hb
  have hg : Differentiable ℂ (fun y : Fin d → ℂ => eval y Q) := fun y =>
    (AnalyticOnNhd.eval_mvPolynomial Q y (Set.mem_univ y)).differentiableAt
  obtain ⟨F, hF, hFf⟩ := IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof d Set.univ
    (fun y => eval y Q) f isOpen_univ hg.differentiableOn
    (fun V hV _ hne => exists_eval_ne_zero_of_isOpen hQ hV hne)
    (by simpa using hf)
    (fun τ _ => by
      refine ⟨Metric.ball τ 1, Metric.ball_mem_nhds τ one_pos, ?_⟩
      refine isBounded_iff_forall_norm_le.2 ⟨|C| * (2 + ‖τ‖) ^ M, ?_⟩
      rintro _ ⟨y, ⟨⟨hy, -⟩, hyQ⟩, rfl⟩
      have hdist : ‖y‖ ≤ ‖τ‖ + 1 := by
        have := norm_le_norm_add_norm_sub' y τ
        rw [Metric.mem_ball, dist_eq_norm] at hy
        linarith
      calc ‖f y‖ ≤ C * (1 + ‖y‖) ^ M := hb y hyQ
        _ ≤ |C| * (1 + ‖y‖) ^ M :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by positivity) _)
        _ ≤ |C| * (2 + ‖τ‖) ^ M :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith) M) (abs_nonneg C))
  have hFd : Differentiable ℂ F := differentiableOn_univ.1 hF
  have hFc : Continuous F := hFd.continuous
  have hclosed : IsClosed {y : Fin d → ℂ | ‖F y‖ ≤ C * (1 + ‖y‖) ^ M} :=
    isClosed_le hFc.norm (continuous_const.mul ((continuous_const.add continuous_norm).pow M))
  have hsub : {y : Fin d → ℂ | eval y Q ≠ 0} ⊆ {y | ‖F y‖ ≤ C * (1 + ‖y‖) ^ M} := by
    intro y hy
    have : F y = f y := hFf ⟨Set.mem_univ y, hy⟩
    show ‖F y‖ ≤ C * (1 + ‖y‖) ^ M
    rw [this]
    exact hb y hy
  have hall : ∀ y, ‖F y‖ ≤ C * (1 + ‖y‖) ^ M := by
    intro y
    have := closure_minimal hsub hclosed
    rw [(dense_eval_ne_zero hQ).closure_eq] at this
    exact this (Set.mem_univ y)
  obtain ⟨p, hp⟩ := h d F C M hFd hall
  exact ⟨p, fun y hy => (hFf ⟨Set.mem_univ y, hy⟩).symm.trans (hp y)⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
