import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Residue

open MeasureTheory Set Filter Topology Metric

namespace GroundTheory.Automorphic

noncomputable section

namespace PseudoEisenstein

/- English proof (translation)
Introduce `s₀ hs₀`. Take `⟨ε, hε, hsub, B, hB, hle⟩` from `hbound s₀ hs₀`. Use `set r := ε / 2 with hr`. Establish `hr0 : 0 < r` using `by rw [hr]; linarith`. Establish `hball : ∀ s ∈ ball s₀ r, closedBall s r ⊆ closedBall s₀ ε`.

Introduce `s hs z hz`. Rewrite `hz`, the goal using `[mem_closedBall]`. Rewrite `hs` using `[mem_ball]`. Combine the equalities or inequalities in the displayed calculation. Establish `hderiv : ∀ x, ∀ s ∈ U, HasDerivAt (fun z => F z x) (deriv (fun z => F z x) s) s` using `fun x s hs => ((hF x).differentiableAt (hU.mem_nhds hs)).hasDerivAt`.

Establish `hF'meas : AEStronglyMeasurable (fun x => deriv (fun z => F z x) s₀) μ`. Establish `hev : ∀ᶠ n : ℕ in atTop, s₀ + ((n : ℂ) + 1)⁻¹ ∈ U`. Establish `ht : Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) atTop (𝓝 s₀)`. Use `tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)` as an intermediate fact. Simplify `(tendsto_const_nhds (x := s₀)).add this` using `[one_div]`.

Conclude with `ht (hU.mem_nhds hs₀)`. Use `set q : ℕ → α → ℂ := fun n x => if s₀ + ((n : ℂ) + 1)⁻¹ ∈ U then ((n : ℂ) + 1) * (F (s₀ + ((n : ℂ) + 1)⁻¹) x - F s₀ x) else 0 with hq`. Use `aestronglyMeasurable_of_tendsto_ae atTop (f := q) (fun n => ?_) (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [hq] split_ifs with h`. Conclude with `aestronglyMeasurable_const.mul ((hmeas _ h).sub (hmeas s₀ hs₀))`.

Conclude with `aestronglyMeasurable_const`. Establish `hsl` using `(hasDerivAt_iff_tendsto_slope.1 (hderiv x s₀ hs₀))`. Establish `hseq : Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) atTop (𝓝[≠] s₀)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩` and prove the remaining obligations. Use `tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)` as an intermediate fact.

Simplify `(tendsto_const_nhds (x := s₀)).add this` using `[one_div]`. Simplify using `only [mem_compl_iff, mem_singleton_iff, add_eq_left, inv_eq_zero]`. Conclude with `Nat.succ_ne_zero n` after adjusting the coercions. Use `(hsl.comp hseq).congr' ?_` and prove the remaining obligations. Use `filter_upwards [hev] with n hn`.

Simplify using `only [hq, Function.comp_apply, if_pos hn, slope, vsub_eq_sub, add_sub_cancel_left, inv_inv, smul_eq_mul]`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₀) (F := F) (F' := fun s x => deriv (fun z => F z x) s) (bound := fun x => B x / r) (ball_mem_nhds s₀ hr0) (eventually_of_mem (hU.mem_nhds hs₀) hmeas) (hB.mono' (hmeas s₀ hs₀) (Eventually.of_forall fun x => hle s₀ …`. Conclude with `key.2.differentiableAt.differentiableWithinAt`. Use `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ fun z hz => hle z (hball s hs (sphere_subset_closedBall hz)) x` and prove the remaining obligations. Use `DifferentiableOn.diffContOnCl ?_` and prove the remaining obligations.

Rewrite using `[closure_ball s hr0.ne']`. Conclude with `(hF x).mono ((hball s hs).trans hsub)`.
-/
theorem differentiableOn_integral_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ∀ x, DifferentiableOn ℂ (fun s => F s x) U)
    (hmeas : ∀ s ∈ U, AEStronglyMeasurable (F s) μ)
    (hbound : ∀ s₀ ∈ U, ∃ ε > 0, closedBall s₀ ε ⊆ U ∧ ∃ B : α → ℝ, Integrable B μ ∧
      ∀ s ∈ closedBall s₀ ε, ∀ x, ‖F s x‖ ≤ B x) :
    DifferentiableOn ℂ (fun s => ∫ x, F s x ∂μ) U := by
  classical
  intro s₀ hs₀
  obtain ⟨ε, hε, hsub, B, hB, hle⟩ := hbound s₀ hs₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : ∀ s ∈ ball s₀ r, closedBall s r ⊆ closedBall s₀ ε := by
    intro s hs z hz
    rw [mem_closedBall] at hz ⊢
    rw [mem_ball] at hs
    calc dist z s₀ ≤ dist z s + dist s s₀ := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hz hs.le
      _ = ε := by rw [hr]; ring
  have hderiv : ∀ x, ∀ s ∈ U, HasDerivAt (fun z => F z x) (deriv (fun z => F z x) s) s :=
    fun x s hs => ((hF x).differentiableAt (hU.mem_nhds hs)).hasDerivAt

  have hF'meas : AEStronglyMeasurable (fun x => deriv (fun z => F z x) s₀) μ := by
    have hev : ∀ᶠ n : ℕ in atTop, s₀ + ((n : ℂ) + 1)⁻¹ ∈ U := by
      have ht : Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) atTop (𝓝 s₀) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa [one_div] using (tendsto_const_nhds (x := s₀)).add this
      exact ht (hU.mem_nhds hs₀)
    set q : ℕ → α → ℂ := fun n x => if s₀ + ((n : ℂ) + 1)⁻¹ ∈ U then
      ((n : ℂ) + 1) * (F (s₀ + ((n : ℂ) + 1)⁻¹) x - F s₀ x) else 0 with hq
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := q) (fun n => ?_)
      (Eventually.of_forall fun x => ?_)
    · simp only [hq]
      split_ifs with h
      · exact aestronglyMeasurable_const.mul ((hmeas _ h).sub (hmeas s₀ hs₀))
      · exact aestronglyMeasurable_const
    · have hsl := (hasDerivAt_iff_tendsto_slope.1 (hderiv x s₀ hs₀))
      have hseq : Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) atTop (𝓝[≠] s₀) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
          simpa [one_div] using (tendsto_const_nhds (x := s₀)).add this
        · simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, inv_eq_zero]
          exact_mod_cast Nat.succ_ne_zero n
      refine (hsl.comp hseq).congr' ?_
      filter_upwards [hev] with n hn
      simp only [hq, Function.comp_apply, if_pos hn, slope, vsub_eq_sub, add_sub_cancel_left,
        inv_inv, smul_eq_mul]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s₀)
    (F := F) (F' := fun s x => deriv (fun z => F z x) s) (bound := fun x => B x / r)
    (ball_mem_nhds s₀ hr0)
    (eventually_of_mem (hU.mem_nhds hs₀) hmeas)
    (hB.mono' (hmeas s₀ hs₀) (Eventually.of_forall fun x => hle s₀ (mem_closedBall_self hε.le) x))
    hF'meas
    (Eventually.of_forall fun x s hs => ?_) (hB.div_const r)
    (Eventually.of_forall fun x s hs => hderiv x s (hsub (hball s hs (mem_closedBall_self hr0.le))))
  · exact key.2.differentiableAt.differentiableWithinAt
  · refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ fun z hz =>
      hle z (hball s hs (sphere_subset_closedBall hz)) x
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s hr0.ne']
    exact (hF x).mono ((hball s hs).trans hsub)

open GroundTheory.Global.Elliptic in

/- English proof (translation)
Use `residue_eq_of_eventuallyEq (u := fun s => ∫ x, A s x ∂μ) (hA.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hε))) ?_` and prove the remaining obligations. Rewrite using `[EventuallyEq, eventually_nhdsWithin_iff]`. Use `filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with s hs hsp`. Rewrite using `[show (fun x => F s x) = fun x => R x * (s - p)⁻¹ + A s x from funext (hFA s hs hsp), integral_add (hR.mul_const _) (hAint s hs), integral_mul_const]`.
-/
theorem residue_integral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {F A : ℂ → α → ℂ}
    {R : α → ℂ} {p : ℂ} {ε : ℝ} (hε : 0 < ε) (hR : Integrable R μ)
    (hA : DifferentiableOn ℂ (fun s => ∫ x, A s x ∂μ) (ball p ε))
    (hAint : ∀ s ∈ ball p ε, Integrable (A s) μ)
    (hFA : ∀ s ∈ ball p ε, s ≠ p → ∀ x, F s x = R x * (s - p)⁻¹ + A s x) :
    residue (fun s => ∫ x, F s x ∂μ) p = ∫ x, R x ∂μ := by
  refine residue_eq_of_eventuallyEq (u := fun s => ∫ x, A s x ∂μ)
    (hA.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hε))) ?_
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with s hs hsp
  rw [show (fun x => F s x) = fun x => R x * (s - p)⁻¹ + A s x from funext (hFA s hs hsp),
    integral_add (hR.mul_const _) (hAint s hs), integral_mul_const]

open GroundTheory.Global.Elliptic in

/- English proof (translation)
Establish `hd : AnalyticAt ℂ (dslope H p) p`. Take `⟨pf, hpf⟩` from `hH`. Conclude with `⟨_, hpf.has_fpower_series_dslope_fslope⟩`. Use `residue_eq_of_eventuallyEq (u := fun z => c * dslope H p z + H z * u z) ((analyticAt_const.mul hd).add (hH.mul hu)) ?_` and prove the remaining obligations. Use `filter_upwards [hΦ, self_mem_nhdsWithin] with z hz hzp`.

Rewrite using `[hz, dslope_of_ne _ hzp, slope_def_field]`. Establish `: z - p ≠ 0` using `sub_ne_zero.2 hzp`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem residue_mul_eq {Φ H u : ℂ → ℂ} {p c : ℂ} (hH : AnalyticAt ℂ H p) (hu : AnalyticAt ℂ u p)
    (hΦ : Φ =ᶠ[𝓝[≠] p] fun z => c * (z - p)⁻¹ + u z) :
    residue (fun z => H z * Φ z) p = H p * c := by
  have hd : AnalyticAt ℂ (dslope H p) p := by
    obtain ⟨pf, hpf⟩ := hH
    exact ⟨_, hpf.has_fpower_series_dslope_fslope⟩
  refine residue_eq_of_eventuallyEq (u := fun z => c * dslope H p z + H z * u z)
    ((analyticAt_const.mul hd).add (hH.mul hu)) ?_
  filter_upwards [hΦ, self_mem_nhdsWithin] with z hz hzp
  rw [hz, dslope_of_ne _ hzp, slope_def_field]
  have : z - p ≠ 0 := sub_ne_zero.2 hzp
  field_simp
  ring

end PseudoEisenstein

end

end GroundTheory.Automorphic
