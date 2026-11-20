import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
open scoped ContDiff

noncomputable section

namespace ChartTaylorCover

/- English proof (translation)
Establish `: 0 ≤ ∑ k ∈ t, 1 / a k` using `Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le`. Check the signs of the components of the expression.
-/
theorem inv_sum_pos {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    0 < (∑ k ∈ t, 1 / a k + 1)⁻¹ := by
  have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
  positivity

/- English proof (translation)
Establish `h1 : 1 / a i ≤ ∑ k ∈ t, 1 / a k` using `Finset.single_le_sum (f := fun k => 1 / a k) (fun k _ => (one_div_pos.2 (ha k)).le) hi`. Establish `h0 : 0 < ∑ k ∈ t, 1 / a k + 1`. Establish `: 0 ≤ ∑ k ∈ t, 1 / a k` using `Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[inv_le_comm₀ h0 (ha i), ← one_div]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_sum_le {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) {i : ι}
    (hi : i ∈ t) : (∑ k ∈ t, 1 / a k + 1)⁻¹ ≤ a i := by
  have h1 : 1 / a i ≤ ∑ k ∈ t, 1 / a k :=
    Finset.single_le_sum (f := fun k => 1 / a k) (fun k _ => (one_div_pos.2 (ha k)).le) hi
  have h0 : 0 < ∑ k ∈ t, 1 / a k + 1 := by
    have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
    linarith
  rw [inv_le_comm₀ h0 (ha i), ← one_div]
  linarith

/- English proof (translation)
Establish `hS : 0 ≤ ∑ i, ‖z i‖ ^ 2` using `by positivity`. Establish `h : ‖z‖ ≤ √(∑ i, ‖z i‖ ^ 2)`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Conclude with `(Real.le_sqrt (norm_nonneg _) hS).2 (Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
  have h : ‖z‖ ≤ √(∑ i, ‖z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    exact (Real.le_sqrt (norm_nonneg _) hS).2
      (Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ (√(∑ i, ‖z i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖z i‖ ^ 2 := Real.sq_sqrt hS

/- English proof (translation)
Use `set s := closedBall y ‖z‖ with hs`. Establish `hconv : Convex ℝ s` using `convex_closedBall _ _`. Establish `hys : y ∈ s` using `mem_closedBall_self (norm_nonneg z)`. Establish `hyzs : y + z ∈ s`. Rewrite using `[hs, mem_closedBall, dist_eq_norm, add_sub_cancel_left]`.

Establish `hM0 : 0 ≤ M` using `le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) y)) (hM y hys)`. Establish `hca : ∀ w ∈ U, ContDiffAt ℝ 2 f w` using `fun w hw => hf.contDiffAt (hU.mem_nhds hw)`. Establish `hd1 : ∀ w ∈ s, DifferentiableAt ℝ f w` using `fun w hw => (hca w (hB hw)).differentiableAt (by norm_num)`. Establish `hd2 : ∀ w ∈ s, DifferentiableAt ℝ (fderiv ℝ f) w` using `fun w hw => ((hca w (hB hw)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Use `set ℓ := fderiv ℝ f y with hℓ`.

Establish `h1 : ∀ w ∈ s, ‖fderiv ℝ f w - ℓ‖ ≤ M * ‖z‖`. Introduce `w hw`. Use `hconv.norm_image_sub_le_of_norm_fderiv_le hd2 hM hys hw` as an intermediate fact. Establish `hw' : ‖w - y‖ ≤ ‖z‖` using `by rwa [hs, mem_closedBall, dist_eq_norm] at hw`. Conclude with `this.trans (mul_le_mul_of_nonneg_left hw' hM0)`.

Establish `hh : ∀ w ∈ s, HasFDerivWithinAt (fun w => f w - ℓ w) (fderiv ℝ f w - ℓ) s w` using `fun w hw => ((hd1 w hw).hasFDerivAt.sub ℓ.hasFDerivAt).hasFDerivWithinAt`. Establish `h2` using `hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hh h1 hys hyzs`. Establish `h3` using `(Real.le_norm_self _).trans h2`. Rewrite `h3` using `[map_add, add_sub_cancel_left]`. Establish `h4 : M * ‖z‖ * ‖z‖ = M * ‖z‖ ^ 2` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem taylor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) {y z : E} {M : ℝ}
    (hB : closedBall y ‖z‖ ⊆ U) (hM : ∀ w ∈ closedBall y ‖z‖, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M) :
    f (y + z) ≤ f y + fderiv ℝ f y z + M * ‖z‖ ^ 2 := by
  set s := closedBall y ‖z‖ with hs
  have hconv : Convex ℝ s := convex_closedBall _ _
  have hys : y ∈ s := mem_closedBall_self (norm_nonneg z)
  have hyzs : y + z ∈ s := by
    rw [hs, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) y)) (hM y hys)
  have hca : ∀ w ∈ U, ContDiffAt ℝ 2 f w := fun w hw => hf.contDiffAt (hU.mem_nhds hw)
  have hd1 : ∀ w ∈ s, DifferentiableAt ℝ f w := fun w hw =>
    (hca w (hB hw)).differentiableAt (by norm_num)
  have hd2 : ∀ w ∈ s, DifferentiableAt ℝ (fderiv ℝ f) w := fun w hw =>
    ((hca w (hB hw)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set ℓ := fderiv ℝ f y with hℓ
  have h1 : ∀ w ∈ s, ‖fderiv ℝ f w - ℓ‖ ≤ M * ‖z‖ := by
    intro w hw
    have := hconv.norm_image_sub_le_of_norm_fderiv_le hd2 hM hys hw
    have hw' : ‖w - y‖ ≤ ‖z‖ := by rwa [hs, mem_closedBall, dist_eq_norm] at hw
    exact this.trans (mul_le_mul_of_nonneg_left hw' hM0)
  have hh : ∀ w ∈ s, HasFDerivWithinAt (fun w => f w - ℓ w) (fderiv ℝ f w - ℓ) s w :=
    fun w hw => ((hd1 w hw).hasFDerivAt.sub ℓ.hasFDerivAt).hasFDerivWithinAt
  have h2 := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hh h1 hys hyzs
  have h3 := (Real.le_norm_self _).trans h2
  rw [map_add, add_sub_cancel_left] at h3
  have h4 : M * ‖z‖ * ‖z‖ = M * ‖z‖ ^ 2 := by ring
  linarith

/- English proof (translation)
The claim follows from `((W.smooth j j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩`.
-/
theorem weight_contDiffOn {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ 2 (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  ((W.smooth j j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

/- English proof (translation)
Introduce `D X _ _ _ _ _ A L W₀ W₁ dV`. Establish `hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source` using `fun p => Classical.choose_spec (A.cover p)`. Establish `hrad : ∀ p : X, ∃ ρ : ℝ, 0 < ρ ∧ closedBall (A.chart (chartIdx A p) p) (2 * ρ) ⊆ (A.chart (chartIdx A p)).target`. Introduce `p`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 (A.chart (chartIdx A p)).open_target _ ((A.chart _).map_source (hsrc p))`.

Conclude with `⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩`. Use `choose ρ hρ hρB using hrad`. Establish `hdens : ∀ p : X, ∃ c : ℝ, 0 < c ∧ ∀ y ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p), c ≤ dV.dens (chartIdx A p) y`. Introduce `p`. Establish `hne : (closedBall (A.chart (chartIdx A p) p) (2 * ρ p)).Nonempty` using `nonempty_closedBall.2 (by linarith [hρ p])`.

Take `⟨y₀, hy₀, hmin⟩` from `(isCompact_closedBall _ _).exists_isMinOn hne ((dV.smooth _).continuousOn.mono (hρB p))`. Conclude with `⟨dV.dens _ y₀, dV.pos _ _ (hρB p hy₀), fun y hy => isMinOn_iff.1 hmin y hy⟩`. Use `choose c hc hcB using hdens`. Establish `hsec : ∀ (W : Weight L) (p : X), ∃ M : ℝ, ∀ w ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p), ‖fderiv ℝ (fderiv ℝ (W.φ (chartIdx A p) ∘ (A.chart (chartIdx A p)).symm)) w‖ ≤ M`. Introduce `W p`.

Establish `hop` using `(A.chart (chartIdx A p)).open_target`. Establish `h1` using `(weight_contDiffOn W (chartIdx A p)).fderiv_of_isOpen hop (m := 1) (by norm_num)`. Conclude with `(isCompact_closedBall _ _).exists_bound_of_continuousOn ((h1.continuousOn_fderiv_of_isOpen hop le_rfl).mono (hρB p))`. Use `choose M hM using hsec`. Set `V : X → Set X` to `fun p => (A.chart (chartIdx A p)).source ∩ (A.chart (chartIdx A p)) ⁻¹' ball (A.chart (chartIdx A p) p) (ρ p)`.

Establish `hVo : ∀ p, IsOpen (V p)` using `fun p => (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source isOpen_ball`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover V hVo (fun p _ => mem_iUnion.2 ⟨p, hsrc p, mem_ball_self (hρ p)⟩)`. Use `set Mt := ∑ p ∈ t, (|M W₀ p| + |M W₁ p|) with hMt`. Establish `hMt0 : 0 ≤ Mt` using `Finset.sum_nonneg fun p _ => by positivity`. Use `⟨(∑ p ∈ t, 1 / ρ p + 1)⁻¹, inv_sum_pos t ρ hρ, Mt, (∑ p ∈ t, 1 / c p + 1)⁻¹, inv_sum_pos t c hc, ?_⟩` and prove the remaining obligations.

Introduce `x`. Take `⟨p, hpt, hxV⟩ : ∃ p ∈ t, x ∈ V p` from `by simpa using ht (mem_univ x)`. Use `set j := chartIdx A p with hj`. Establish `hxs : x ∈ (A.chart j).source` using `hxV.1`. Establish `hxb : A.chart j x ∈ ball (A.chart j p) (ρ p)` using `hxV.2`.

Establish `hr` using `inv_sum_le t ρ hρ hpt`. Establish `hsub : closedBall (A.chart j x) (∑ p ∈ t, 1 / ρ p + 1)⁻¹ ⊆ closedBall (A.chart j p) (2 * ρ p)`. Use `closedBall_subset_closedBall' ?_` and prove the remaining obligations. Use `mem_ball.1 hxb` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨j, hxs, hsub.trans (hρB p), fun y hy => (inv_sum_le t c hc hpt).trans (hcB p y (hsub hy)), ?_⟩` and prove the remaining obligations. Establish `key : ∀ W : Weight L, |M W p| ≤ Mt → ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ, ‖z‖ ≤ (∑ p ∈ t, 1 / ρ p + 1)⁻¹ → W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + Mt * ∑ i, ‖z i‖ ^ 2`. Introduce `W hWM`. Use `⟨fderiv ℝ (W.φ j ∘ (A.chart j).symm) (A.chart j x), fun z hz => ?_⟩` and prove the remaining obligations. Establish `hzB : closedBall (A.chart j x) ‖z‖ ⊆ closedBall (A.chart j p) (2 * ρ p)` using `(closedBall_subset_closedBall hz).trans hsub`.

Establish `hT` using `taylor_le (A.chart j).open_target (weight_contDiffOn W j) (hzB.trans (hρB p)) (fun w hw => (hM W p w (hzB hw)).trans (le_abs_self _))`. Establish `hx' : (W.φ j ∘ (A.chart j).symm) (A.chart j x) = W.φ j x`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hxs]`. Rewrite `hT` using `[hx']`. Establish `h1 : |M W p| * ‖z‖ ^ 2 ≤ Mt * ‖z‖ ^ 2` using `mul_le_mul_of_nonneg_right hWM (by positivity)`.

Establish `h2 : Mt * ‖z‖ ^ 2 ≤ Mt * ∑ i, ‖z i‖ ^ 2` using `mul_le_mul_of_nonneg_left (norm_sq_le_sum z) hMt0`. Simplify using `only [Function.comp_apply] at hT`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `W hW`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hW`.

Break down `hW with rfl | rfl` into its components or cases. Use `key _ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `key _ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem proof : ChartTaylorCover.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)

  have hrad : ∀ p : X, ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (A.chart (chartIdx A p) p) (2 * ρ) ⊆ (A.chart (chartIdx A p)).target := by
    intro p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (A.chart (chartIdx A p)).open_target _
      ((A.chart _).map_source (hsrc p))
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩
  choose ρ hρ hρB using hrad

  have hdens : ∀ p : X, ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p), c ≤ dV.dens (chartIdx A p) y := by
    intro p
    have hne : (closedBall (A.chart (chartIdx A p) p) (2 * ρ p)).Nonempty :=
      nonempty_closedBall.2 (by linarith [hρ p])
    obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall _ _).exists_isMinOn hne
      ((dV.smooth _).continuousOn.mono (hρB p))
    exact ⟨dV.dens _ y₀, dV.pos _ _ (hρB p hy₀), fun y hy => isMinOn_iff.1 hmin y hy⟩
  choose c hc hcB using hdens

  have hsec : ∀ (W : Weight L) (p : X), ∃ M : ℝ,
      ∀ w ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p),
        ‖fderiv ℝ (fderiv ℝ (W.φ (chartIdx A p) ∘ (A.chart (chartIdx A p)).symm)) w‖ ≤ M := by
    intro W p
    have hop := (A.chart (chartIdx A p)).open_target
    have h1 := (weight_contDiffOn W (chartIdx A p)).fderiv_of_isOpen hop (m := 1) (by norm_num)
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((h1.continuousOn_fderiv_of_isOpen hop le_rfl).mono (hρB p))
  choose M hM using hsec

  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' ball (A.chart (chartIdx A p) p) (ρ p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hsrc p, mem_ball_self (hρ p)⟩)
  set Mt := ∑ p ∈ t, (|M W₀ p| + |M W₁ p|) with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun p _ => by positivity
  refine ⟨(∑ p ∈ t, 1 / ρ p + 1)⁻¹, inv_sum_pos t ρ hρ, Mt, (∑ p ∈ t, 1 / c p + 1)⁻¹,
    inv_sum_pos t c hc, ?_⟩
  intro x
  obtain ⟨p, hpt, hxV⟩ : ∃ p ∈ t, x ∈ V p := by simpa using ht (mem_univ x)
  set j := chartIdx A p with hj
  have hxs : x ∈ (A.chart j).source := hxV.1
  have hxb : A.chart j x ∈ ball (A.chart j p) (ρ p) := hxV.2
  have hr := inv_sum_le t ρ hρ hpt
  have hsub : closedBall (A.chart j x) (∑ p ∈ t, 1 / ρ p + 1)⁻¹ ⊆
      closedBall (A.chart j p) (2 * ρ p) := by
    refine closedBall_subset_closedBall' ?_
    have := mem_ball.1 hxb
    linarith
  refine ⟨j, hxs, hsub.trans (hρB p), fun y hy => (inv_sum_le t c hc hpt).trans (hcB p y (hsub hy)),
    ?_⟩

  have key : ∀ W : Weight L, |M W p| ≤ Mt → ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ,
      ‖z‖ ≤ (∑ p ∈ t, 1 / ρ p + 1)⁻¹ →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + Mt * ∑ i, ‖z i‖ ^ 2 := by
    intro W hWM
    refine ⟨fderiv ℝ (W.φ j ∘ (A.chart j).symm) (A.chart j x), fun z hz => ?_⟩
    have hzB : closedBall (A.chart j x) ‖z‖ ⊆ closedBall (A.chart j p) (2 * ρ p) :=
      (closedBall_subset_closedBall hz).trans hsub
    have hT := taylor_le (A.chart j).open_target (weight_contDiffOn W j) (hzB.trans (hρB p))
      (fun w hw => (hM W p w (hzB hw)).trans (le_abs_self _))
    have hx' : (W.φ j ∘ (A.chart j).symm) (A.chart j x) = W.φ j x := by
      simp only [Function.comp_apply, (A.chart j).left_inv hxs]
    rw [hx'] at hT
    have h1 : |M W p| * ‖z‖ ^ 2 ≤ Mt * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hWM (by positivity)
    have h2 : Mt * ‖z‖ ^ 2 ≤ Mt * ∑ i, ‖z i‖ ^ 2 := mul_le_mul_of_nonneg_left (norm_sq_le_sum z) hMt0
    simp only [Function.comp_apply] at hT
    linarith
  intro W hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases hW with rfl | rfl
  · refine key _ ?_
    calc |M W p| ≤ |M W p| + |M W₁ p| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W p| + |M W₁ p|)
          (fun k _ => by positivity) hpt
  · refine key _ ?_
    calc |M W p| ≤ |M W₀ p| + |M W p| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W₀ p| + |M W p|)
          (fun k _ => by positivity) hpt

end ChartTaylorCover

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
