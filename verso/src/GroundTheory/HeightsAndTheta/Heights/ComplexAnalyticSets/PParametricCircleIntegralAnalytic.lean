import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametricCircleIntegralAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Metric Filter Topology Set Complex MeasureTheory

open scoped Real

noncomputable section

namespace ParametricCircleIntegralAnalytic

/- English proof (translation)
Set `e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)` to `ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm`. Establish `hO' : IsOpen (e.symm ⁻¹' O)` using `hO.preimage e.symm.continuous`. Establish `hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' O)` using `hf.comp e.symm.differentiableOn (fun y hy => hy)`. Establish `ha` using `RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hO' hg`. Introduce `x hx`.

Establish `h1 : AnalyticAt ℂ (f ∘ e.symm) (e x)` using `ha (e x) (by simpa using hx)`. Establish `h2` using `h1.comp (ContinuousLinearMap.analyticAt (e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) x)`. Simplify `h2` using `[Function.comp_def]`.
-/
theorem analyticOnNhd_of_differentiableOn_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {O : Set E} {f : E → ℂ} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    AnalyticOnNhd ℂ f O := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  have hO' : IsOpen (e.symm ⁻¹' O) := hO.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' O) :=
    hf.comp e.symm.differentiableOn (fun y hy => hy)
  have ha := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hO' hg
  intro x hx
  have h1 : AnalyticAt ℂ (f ∘ e.symm) (e x) := ha (e x) (by simpa using hx)
  have h2 := h1.comp (ContinuousLinearMap.analyticAt (e : E →L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) x)
  simpa [Function.comp_def] using h2

end ParametricCircleIntegralAnalytic

open ParametricCircleIntegralAnalytic in

/- English proof (translation)
Introduce `ι _ Φ O U c r hr hO hU hΦ hUO x₀ hx₀`. Establish `hcd : ContinuousOn (fderiv ℂ Φ) O` using `((analyticOnNhd_of_differentiableOn_fd hO hΦ).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hO le_rfl`. Take `⟨u, v, hu, -, hx₀u, hsv, huv⟩` from `generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hO (by rintro ⟨x, s⟩ ⟨hx, hs⟩; obtain rfl : x = x₀ := hx; exact hUO x hx₀ s hs)`. Take `⟨ε, hε, hεu⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds (hx₀u rfl))`. Establish `hK : closedBall x₀ ε ×ˢ sphere c r ⊆ O` using `fun p hp => huv ⟨hεu hp.1, hsv hp.2⟩`.

Take `⟨M, hM⟩` from `((isCompact_closedBall x₀ ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn (hcd.mono hK)`. Establish `hmem : ∀ x ∈ closedBall x₀ ε, ∀ θ : ℝ, (x, circleMap c r θ) ∈ O` using `fun x hx θ => hK ⟨hx, circleMap_mem_sphere c hr θ⟩`. Establish `hcont : ∀ x ∈ closedBall x₀ ε, Continuous fun θ : ℝ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ)` using `fun x hx => (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul (hΦ.continuousOn.comp_continuous (by fun_prop) (hmem x hx))`. Establish `hdiff : DifferentiableOn ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) (ball x₀ ε)`. Introduce `x₁ hx₁`.

Establish `hs : ball x₀ ε ∈ 𝓝 x₁` using `isOpen_ball.mem_nhds hx₁`. Establish `hx₁c : x₁ ∈ closedBall x₀ ε` using `ball_subset_closedBall hx₁`. Simplify using `only [circleIntegral, deriv_circleMap]`. Use `(intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0) (b := 2 * π) (F := fun x θ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ)) (F' := fun x θ => (circleMap 0 r θ * I) • (fderiv ℂ Φ (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ …` and prove the remaining obligations. Use `filter_upwards [hs] with x hx`.

Conclude with `(hcont x (ball_subset_closedBall hx)).aestronglyMeasurable`. Conclude with `(hcont x₁ hx₁c).intervalIntegrable _ _`. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `(by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul ((ContinuousLinearMap.compL ℂ (ι → ℂ) ((ι → ℂ) × ℂ) ℂ).flip (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) |>.continuous.comp (hcd.comp_continuous (by fun_prop) (hmem x₁ hx₁c)))`. Use `Eventually.of_forall fun θ _ x hx => ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]`. Use `mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)` and prove the remaining obligations. Use `(ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))` and prove the remaining obligations. Conclude with `hM _ ⟨ball_subset_closedBall hx, circleMap_mem_sphere c hr θ⟩`. Conclude with `intervalIntegrable_const`.

Use `Eventually.of_forall fun θ _ x hx => ?_` and prove the remaining obligations. Establish `h1 : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap c r θ)) (x, circleMap c r θ)` using `(hΦ.differentiableAt (hO.mem_nhds (hmem x (ball_subset_closedBall hx) θ))).hasFDerivAt`. Conclude with `(h1.comp x (hasFDerivAt_prodMk_left x (circleMap c r θ))).const_smul (circleMap 0 r θ * I)`. Conclude with `analyticOnNhd_of_differentiableOn_fd isOpen_ball hdiff x₀ (mem_ball_self hε)`.
-/
theorem ParametricCircleIntegralAnalytic.proof : ParametricCircleIntegralAnalytic.Statement := by
  intro ι _ Φ O U c r hr hO hU hΦ hUO x₀ hx₀
  have hcd : ContinuousOn (fderiv ℂ Φ) O :=
    ((analyticOnNhd_of_differentiableOn_fd hO hΦ).contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hO le_rfl
  obtain ⟨u, v, hu, -, hx₀u, hsv, huv⟩ := generalized_tube_lemma isCompact_singleton (isCompact_sphere c r) hO
    (by rintro ⟨x, s⟩ ⟨hx, hs⟩; obtain rfl : x = x₀ := hx; exact hUO x hx₀ s hs)
  obtain ⟨ε, hε, hεu⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hu.mem_nhds (hx₀u rfl))
  have hK : closedBall x₀ ε ×ˢ sphere c r ⊆ O := fun p hp => huv ⟨hεu hp.1, hsv hp.2⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ ε).prod (isCompact_sphere c r)).exists_bound_of_continuousOn
    (hcd.mono hK)
  have hmem : ∀ x ∈ closedBall x₀ ε, ∀ θ : ℝ, (x, circleMap c r θ) ∈ O := fun x hx θ =>
    hK ⟨hx, circleMap_mem_sphere c hr θ⟩
  have hcont : ∀ x ∈ closedBall x₀ ε,
      Continuous fun θ : ℝ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ) := fun x hx =>
    (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
      (hΦ.continuousOn.comp_continuous (by fun_prop) (hmem x hx))
  have hdiff : DifferentiableOn ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) (ball x₀ ε) := by
    intro x₁ hx₁
    have hs : ball x₀ ε ∈ 𝓝 x₁ := isOpen_ball.mem_nhds hx₁
    have hx₁c : x₁ ∈ closedBall x₀ ε := ball_subset_closedBall hx₁
    simp only [circleIntegral, deriv_circleMap]
    refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
      (b := 2 * π) (F := fun x θ => (circleMap 0 r θ * I) • Φ (x, circleMap c r θ))
      (F' := fun x θ => (circleMap 0 r θ * I) •
        (fderiv ℂ Φ (x, circleMap c r θ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ))
      (bound := fun _ => |r| * (M * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖)) hs ?_ ?_ ?_ ?_ ?_
      ?_).differentiableAt.differentiableWithinAt
    · filter_upwards [hs] with x hx
      exact (hcont x (ball_subset_closedBall hx)).aestronglyMeasurable
    · exact (hcont x₁ hx₁c).intervalIntegrable _ _
    · refine Continuous.aestronglyMeasurable ?_
      exact (by fun_prop : Continuous fun θ : ℝ => circleMap 0 r θ * I).smul
        ((ContinuousLinearMap.compL ℂ (ι → ℂ) ((ι → ℂ) × ℂ) ℂ).flip
          (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) |>.continuous.comp
          (hcd.comp_continuous (by fun_prop) (hmem x₁ hx₁c)))
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact hM _ ⟨ball_subset_closedBall hx, circleMap_mem_sphere c hr θ⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt Φ (fderiv ℂ Φ (x, circleMap c r θ)) (x, circleMap c r θ) :=
        (hΦ.differentiableAt (hO.mem_nhds (hmem x (ball_subset_closedBall hx) θ))).hasFDerivAt
      exact (h1.comp x (hasFDerivAt_prodMk_left x (circleMap c r θ))).const_smul (circleMap 0 r θ * I)
  exact analyticOnNhd_of_differentiableOn_fd isOpen_ball hdiff x₀ (mem_ball_self hε)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
