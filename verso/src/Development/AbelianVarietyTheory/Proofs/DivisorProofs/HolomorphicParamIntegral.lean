import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `s₁ hs₁`. Establish `hs₁' : dist s₁ s₀ < r` using `hs₁`. Use `set ε : ℝ := (r - dist s₁ s₀) / 2 with hε`. Establish `εpos : 0 < ε` using `by rw [hε]; linarith`. Establish `hsub : ∀ y ∈ Metric.ball s₁ ε, Metric.closedBall y ε ⊆ Metric.ball s₀ r`.

Introduce `y hy z hz`. Rewrite `hy`, the goal using `[Metric.mem_ball]`. Rewrite `hz` using `[Metric.mem_closedBall]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[dist_triangle z y s₀, dist_triangle y s₁ s₀]`.

Use `_ < r := by linarith`. Establish `hball : Metric.ball s₁ ε ⊆ Metric.ball s₀ r` using `fun y hy => hsub y hy (Metric.mem_closedBall_self εpos.le)`. Establish `hDA : ∀ x, ∀ y ∈ Metric.ball s₀ r, HasDerivAt (fun s => F s x) (deriv (fun s => F s x) y) y` using `fun x y hy => ((hdiff x).differentiableAt (Metric.isOpen_ball.mem_nhds hy)).hasDerivAt`. Establish `hbound : ∀ x, ∀ y ∈ Metric.ball s₁ ε, ‖deriv (fun s => F s x) y‖ ≤ M / ε`. Introduce `x y hy`.

Apply `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le εpos` to reduce the goal to its premises. Conclude with `(hdiff x).diffContOnCl_ball (hsub y hy)`. Introduce `z hz`. Conclude with `hbd z (hsub y hy (Metric.sphere_subset_closedBall hz)) x`. Establish `hF'meas : AEStronglyMeasurable (fun x => deriv (fun s => F s x) s₁) ρ`.

Set `h : ℕ → ℂ` to `fun n => ((ε / ((n : ℝ) + 2) : ℝ) : ℂ)`. Establish `hpos : ∀ n : ℕ, 0 < ε / ((n : ℝ) + 2)` using `fun n => by positivity`. Establish `hmem : ∀ n, s₁ + h n ∈ Metric.ball s₀ r`. Introduce `n`. Apply `hball` to reduce the goal to its premises.

Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]`. Simplify using `only [h, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[abs_of_pos (hpos n), div_lt_iff₀ (by positivity)]`. Use polynomial arithmetic with `[(n.cast_nonneg : (0 : ℝ) ≤ n)]`. Establish `htend : Tendsto h atTop (𝓝[≠] 0)`.

Use `tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0)` using `tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)`. Establish `h2` using `(Complex.continuous_ofReal.tendsto 0).comp h1`. Conclude with `h2`. Simplify using `only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, h]`.

Conclude with `Complex.ofReal_ne_zero.2 (hpos n).ne'`. Use `aestronglyMeasurable_of_tendsto_ae atTop (f := fun n x => (h n)⁻¹ • (F (s₁ + h n) x - F s₁ x)) (fun n => ?_) ?_` and prove the remaining obligations. Conclude with `((hmeas _ (hmem n)).sub (hmeas _ hs₁)).const_smul (h n)⁻¹`. Conclude with `ae_of_all _ fun x => (hasDerivAt_iff_tendsto_slope_zero.1 (hDA x s₁ hs₁)).comp htend`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) (F := F) (F' := fun y x => deriv (fun s => F s x) y) (x₀ := s₁) (bound := fun _ => M / ε) (Metric.ball_mem_nhds s₁ εpos) (Eventually.mono (Metric.isOpen_ball.mem_nhds hs₁) (fun y hy => hmeas y hy)) (Integrable.of_bound (hm …`.

Conclude with `key.2.differentiableAt.differentiableWithinAt`.
-/
theorem differentiableOn_integral_of_bounded_holomorphic {X : Type} [MeasurableSpace X]
    (ρ : Measure X) [IsFiniteMeasure ρ] (F : ℂ → X → ℂ) (s₀ : ℂ) (r M : ℝ)
    (hmeas : ∀ s ∈ Metric.ball s₀ r, AEStronglyMeasurable (F s) ρ)
    (hdiff : ∀ x, DifferentiableOn ℂ (fun s => F s x) (Metric.ball s₀ r))
    (hbd : ∀ s ∈ Metric.ball s₀ r, ∀ x, ‖F s x‖ ≤ M) :
    DifferentiableOn ℂ (fun s => ∫ x, F s x ∂ρ) (Metric.ball s₀ r) := by
  intro s₁ hs₁
  have hs₁' : dist s₁ s₀ < r := hs₁
  set ε : ℝ := (r - dist s₁ s₀) / 2 with hε
  have εpos : 0 < ε := by rw [hε]; linarith
  have hsub : ∀ y ∈ Metric.ball s₁ ε, Metric.closedBall y ε ⊆ Metric.ball s₀ r := by
    intro y hy z hz
    rw [Metric.mem_ball] at hy ⊢
    rw [Metric.mem_closedBall] at hz
    calc dist z s₀ ≤ dist z y + dist y s₁ + dist s₁ s₀ := by
          linarith [dist_triangle z y s₀, dist_triangle y s₁ s₀]
      _ < r := by linarith
  have hball : Metric.ball s₁ ε ⊆ Metric.ball s₀ r := fun y hy =>
    hsub y hy (Metric.mem_closedBall_self εpos.le)
  have hDA : ∀ x, ∀ y ∈ Metric.ball s₀ r,
      HasDerivAt (fun s => F s x) (deriv (fun s => F s x) y) y :=
    fun x y hy => ((hdiff x).differentiableAt (Metric.isOpen_ball.mem_nhds hy)).hasDerivAt
  have hbound : ∀ x, ∀ y ∈ Metric.ball s₁ ε, ‖deriv (fun s => F s x) y‖ ≤ M / ε := by
    intro x y hy
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le εpos
    · exact (hdiff x).diffContOnCl_ball (hsub y hy)
    · intro z hz
      exact hbd z (hsub y hy (Metric.sphere_subset_closedBall hz)) x
  have hF'meas : AEStronglyMeasurable (fun x => deriv (fun s => F s x) s₁) ρ := by
    let h : ℕ → ℂ := fun n => ((ε / ((n : ℝ) + 2) : ℝ) : ℂ)
    have hpos : ∀ n : ℕ, 0 < ε / ((n : ℝ) + 2) := fun n => by positivity
    have hmem : ∀ n, s₁ + h n ∈ Metric.ball s₀ r := by
      intro n
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      simp only [h, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (hpos n), div_lt_iff₀ (by positivity)]
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have htend : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        exact h2
      · simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, h]
        exact Complex.ofReal_ne_zero.2 (hpos n).ne'
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x => (h n)⁻¹ • (F (s₁ + h n) x - F s₁ x)) (fun n => ?_) ?_
    · exact ((hmeas _ (hmem n)).sub (hmeas _ hs₁)).const_smul (h n)⁻¹
    · exact ae_of_all _ fun x =>
        (hasDerivAt_iff_tendsto_slope_zero.1 (hDA x s₁ hs₁)).comp htend
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) (F := F)
    (F' := fun y x => deriv (fun s => F s x) y) (x₀ := s₁) (bound := fun _ => M / ε)
    (Metric.ball_mem_nhds s₁ εpos)
    (Eventually.mono (Metric.isOpen_ball.mem_nhds hs₁) (fun y hy => hmeas y hy))
    (Integrable.of_bound (hmeas s₁ hs₁) M (ae_of_all _ fun x => hbd s₁ hs₁ x))
    hF'meas
    (ae_of_all _ fun x y hy => hbound x y hy)
    (integrable_const _)
    (ae_of_all _ fun x y hy => hDA x y (hball hy))
  exact key.2.differentiableAt.differentiableWithinAt

/- English proof (translation)
Introduce `α β _ _ μ ν _ _ θ H s₀ r M h1 h2 h3`. Establish `hd` using `differentiableOn_integral_of_bounded_holomorphic (ν.prod μ) (fun s p => θ p.1 p.2 * H s p.2) s₀ r M h1 (fun p => (h2 p.2).const_mul _) (fun s hs p => h3 s hs p.1 p.2)`. Use `hd.congr fun s hs => ?_` and prove the remaining obligations. Conclude with `(integral_prod _ (Integrable.of_bound (h1 s hs) M (ae_of_all _ fun p => h3 s hs p.1 p.2))).symm`.
-/
theorem differentiableOn_double_integral_of_bounded_holomorphic :
    ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (θ : β → α → ℂ) (H : ℂ → α → ℂ) (s₀ : ℂ) (r M : ℝ),
    (∀ s ∈ Metric.ball s₀ r, AEStronglyMeasurable (fun p : β × α => θ p.1 p.2 * H s p.2) (ν.prod μ)) →
    (∀ a, DifferentiableOn ℂ (fun s => H s a) (Metric.ball s₀ r)) →
    (∀ s ∈ Metric.ball s₀ r, ∀ b a, ‖θ b a * H s a‖ ≤ M) →
    DifferentiableOn ℂ (fun s => ∫ b, ∫ a, θ b a * H s a ∂μ ∂ν) (Metric.ball s₀ r) := by
  intro α β _ _ μ ν _ _ θ H s₀ r M h1 h2 h3
  have hd := differentiableOn_integral_of_bounded_holomorphic (ν.prod μ)
    (fun s p => θ p.1 p.2 * H s p.2) s₀ r M h1 (fun p => (h2 p.2).const_mul _)
    (fun s hs p => h3 s hs p.1 p.2)
  refine hd.congr fun s hs => ?_
  exact (integral_prod _ (Integrable.of_bound (h1 s hs) M
    (ae_of_all _ fun p => h3 s hs p.1 p.2))).symm

end GlobalTheory
