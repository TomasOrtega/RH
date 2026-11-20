import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.HoloLog

/- English proof (translation)
Establish `hfc : ContinuousAt f x₀` using `hf.continuousAt (hV.mem_nhds hx₀)`. Establish `hev : ∀ᶠ x in nhds x₀, x ∈ V ∧ dist (f x) (f x₀) < 1` using `Filter.Eventually.and (show ∀ᶠ x in nhds x₀, x ∈ V from hV.mem_nhds hx₀) (Metric.continuousAt_iff'.1 hfc 1 one_pos)`. Establish `hx0 : h x₀ ≠ 0` using `h0 x₀ hx₀`. Establish `heq : f =ᶠ[nhds x₀] fun x => f x₀ + Complex.log (h x / h x₀)` using `by filter_upwards [hev] with x hx`. Establish `hsm : ‖f x - f x₀‖ < 1` using `by rw [← dist_eq_norm]; exact hx.2`.

Establish `him : |(f x - f x₀).im| < 1` using `lt_of_le_of_lt (Complex.abs_im_le_norm _) hsm`. Establish `hq : h x / h x₀ = Complex.exp (f x - f x₀)`. Rewrite using `[Complex.exp_sub, he x hx.1, he x₀ hx₀]`. Rewrite using `[hq, Complex.log_exp]`. Expand and normalize the polynomial expressions, which then agree.

Use `(abs_lt.1 him).1` as an intermediate fact. Combine the linear relations using `[Real.pi_gt_three]`. Use `(abs_lt.1 him).2` as an intermediate fact. Combine the linear relations using `[Real.pi_gt_three]`. Use `DifferentiableAt.congr_of_eventuallyEq ?_ heq` and prove the remaining obligations.

Establish `hd : DifferentiableAt ℂ h x₀` using `hh.differentiableAt (hV.mem_nhds hx₀)`. Establish `hslit : h x₀ / h x₀ ∈ Complex.slitPlane`. Rewrite using `[div_self hx0]`. Conclude with `Complex.one_mem_slitPlane`. Establish `hq : DifferentiableAt ℂ (fun x => h x / h x₀) x₀`.

Simplify `hd.mul_const (h x₀)⁻¹` using `only [div_eq_mul_inv]`. Establish `hl : DifferentiableAt ℂ (Complex.log ∘ fun x => h x / h x₀) x₀` using `(Complex.hasStrictDerivAt_log hslit).hasDerivAt.differentiableAt.comp x₀ hq`. Conclude with `(differentiableAt_const _).add hl`.
-/
theorem differentiableAt_of_exp_eq {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {V : Set F} (hV : IsOpen V) {h f : F → ℂ} (hh : DifferentiableOn ℂ h V)
    (h0 : ∀ x ∈ V, h x ≠ 0) (hf : ContinuousOn f V) (he : ∀ x ∈ V, Complex.exp (f x) = h x)
    {x₀ : F} (hx₀ : x₀ ∈ V) : DifferentiableAt ℂ f x₀ := by
  have hfc : ContinuousAt f x₀ := hf.continuousAt (hV.mem_nhds hx₀)
  have hev : ∀ᶠ x in nhds x₀, x ∈ V ∧ dist (f x) (f x₀) < 1 :=
    Filter.Eventually.and (show ∀ᶠ x in nhds x₀, x ∈ V from hV.mem_nhds hx₀) (Metric.continuousAt_iff'.1 hfc 1 one_pos)
  have hx0 : h x₀ ≠ 0 := h0 x₀ hx₀
  have heq : f =ᶠ[nhds x₀] fun x => f x₀ + Complex.log (h x / h x₀) := by
    filter_upwards [hev] with x hx
    have hsm : ‖f x - f x₀‖ < 1 := by rw [← dist_eq_norm]; exact hx.2
    have him : |(f x - f x₀).im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm _) hsm
    have hq : h x / h x₀ = Complex.exp (f x - f x₀) := by
      rw [Complex.exp_sub, he x hx.1, he x₀ hx₀]
    rw [hq, Complex.log_exp]
    · ring
    · have := (abs_lt.1 him).1; linarith [Real.pi_gt_three]
    · have := (abs_lt.1 him).2; linarith [Real.pi_gt_three]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hd : DifferentiableAt ℂ h x₀ := hh.differentiableAt (hV.mem_nhds hx₀)
  have hslit : h x₀ / h x₀ ∈ Complex.slitPlane := by
    rw [div_self hx0]; exact Complex.one_mem_slitPlane
  have hq : DifferentiableAt ℂ (fun x => h x / h x₀) x₀ := by
    simpa only [div_eq_mul_inv] using hd.mul_const (h x₀)⁻¹
  have hl : DifferentiableAt ℂ (Complex.log ∘ fun x => h x / h x₀) x₀ :=
    (Complex.hasStrictDerivAt_log hslit).hasDerivAt.differentiableAt.comp x₀ hq
  exact (differentiableAt_const _).add hl

/- English proof (translation)
Introduce `F _ _ V hVo hVc h hh h0`. Break down `V.eq_empty_or_nonempty with hne | hne` into its components or cases. Conclude with `⟨0, by simp [hne], by simp [hne]⟩`. Establish `hsc : IsSimplyConnected V` using `by haveI : ContractibleSpace V := hVc.contractibleSpace hne`. Conclude with `(inferInstance : SimplyConnectedSpace V)`.

Take `⟨f, hfc, hfe⟩` from `Complex.exists_continuousOn_eqOn_exp_comp hsc hVo hh.continuousOn (fun ⟨x, hx, hx0⟩ => h0 x hx hx0)`. Establish `he : ∀ x ∈ V, Complex.exp (f x) = h x` using `fun x hx => hfe hx`. Use `⟨f, fun x hx => (differentiableAt_of_exp_eq hVo hh h0 hfc he hx).differentiableWithinAt, fun x hx => (he x hx).symm⟩` and prove the remaining obligations.
-/
theorem main : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set F}, IsOpen V → Convex ℝ V → ∀ h : F → ℂ, DifferentiableOn ℂ h V → (∀ x ∈ V, h x ≠ 0) → ∃ a : F → ℂ, DifferentiableOn ℂ a V ∧ ∀ x ∈ V, h x = Complex.exp (a x) := by
  intro F _ _ V hVo hVc h hh h0
  rcases V.eq_empty_or_nonempty with hne | hne
  · exact ⟨0, by simp [hne], by simp [hne]⟩
  have hsc : IsSimplyConnected V := by
    haveI : ContractibleSpace V := hVc.contractibleSpace hne
    exact (inferInstance : SimplyConnectedSpace V)
  obtain ⟨f, hfc, hfe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc hVo hh.continuousOn
    (fun ⟨x, hx, hx0⟩ => h0 x hx hx0)
  have he : ∀ x ∈ V, Complex.exp (f x) = h x := fun x hx => hfe hx
  refine ⟨f, fun x hx => (differentiableAt_of_exp_eq hVo hh h0 hfc he hx).differentiableWithinAt,
    fun x hx => (he x hx).symm⟩

end GlobalTheory.HoloLog
