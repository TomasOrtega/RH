import Mathlib

open Complex MeasureTheory intervalIntegral Filter Topology Set
open UpperHalfPlane hiding I I_re I_im
open scoped Manifold Interval

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

/- English proof (translation)
Establish `hsub : [[x₀, x₀ + T]] ×ℂ [[y₁, y₂]] ⊆ {w : ℂ | 0 < w.im}`. Introduce `w hw`. Rewrite `hw` using `[mem_reProdIm]`. Use `hw.2` as an intermediate fact. Rewrite `this` using `[Set.mem_uIcc]`.

Use `show 0 < w.im`. Break down `this with h | h` into its components or cases. Conclude with `lt_of_lt_of_le hy₁ h.1`. Conclude with `lt_of_lt_of_le hy₂ h.1`. Establish `H` using `integral_boundary_rect_eq_zero_of_differentiableOn G (x₀ + y₁ * I) ((x₀ + T : ℝ) + y₂ * I) (by`.

Use `hG.mono (Set.Subset.trans ?_ hsub)` and prove the remaining obligations. Use the proof step `simp)`. Simplify using `only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add] at H`. Establish `hv : ∫ y in y₁..y₂, G (((x₀ + T : ℝ) : ℂ) + y * I) = ∫ y in y₁..y₂, G ((x₀ : ℂ) + y * I)`. Use `intervalIntegral.integral_congr fun y hy => ?_` and prove the remaining obligations.

Establish `hy0 : 0 < y`. Rewrite `hy` using `[Set.mem_uIcc]`. Break down `hy with h | h` into its components or cases. Conclude with `lt_of_lt_of_le hy₁ h.1`. Conclude with `lt_of_lt_of_le hy₂ h.1`.

Use `hper ((x₀ : ℂ) + y * I) (by simpa using hy0)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `H` using `[hv, add_sub_cancel_right, sub_eq_zero]`. Conclude with `H`.
-/
theorem integral_periodic_eq_of_im {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {w | 0 < w.im}) {T : ℝ}
    (hper : ∀ w : ℂ, 0 < w.im → G (w + T) = G w) (x₀ : ℝ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) :
    ∫ x in x₀..x₀ + T, G (x + y₁ * I) = ∫ x in x₀..x₀ + T, G (x + y₂ * I) := by
  have hsub : [[x₀, x₀ + T]] ×ℂ [[y₁, y₂]] ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    rw [mem_reProdIm] at hw
    have := hw.2
    rw [Set.mem_uIcc] at this
    show 0 < w.im
    rcases this with h | h
    · exact lt_of_lt_of_le hy₁ h.1
    · exact lt_of_lt_of_le hy₂ h.1
  have H := integral_boundary_rect_eq_zero_of_differentiableOn G (x₀ + y₁ * I)
    ((x₀ + T : ℝ) + y₂ * I) (by
      refine hG.mono (Set.Subset.trans ?_ hsub)
      simp)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at H
  have hv : ∫ y in y₁..y₂, G (((x₀ + T : ℝ) : ℂ) + y * I) = ∫ y in y₁..y₂, G ((x₀ : ℂ) + y * I) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : 0 < y := by
      rw [Set.mem_uIcc] at hy
      rcases hy with h | h
      · exact lt_of_lt_of_le hy₁ h.1
      · exact lt_of_lt_of_le hy₂ h.1
    have := hper ((x₀ : ℂ) + y * I) (by simpa using hy0)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [hv, add_sub_cancel_right, sub_eq_zero] at H
  exact H

/- English proof (translation)
Use `set G : ℂ → ℂ := F ∘ ofComplex`. Establish `hG : DifferentiableOn ℂ G {w | 0 < w.im}` using `mdifferentiable_iff.1 hF`. Establish `hGw : ∀ w : ℂ, (hw : 0 < w.im) → G w = F ⟨w, hw⟩` using `fun w hw => by`. Simplify using `only [G, Function.comp_apply, ofComplex_apply_of_im_pos hw]`. Establish `hper' : ∀ w : ℂ, 0 < w.im → G (w + T) = G w` using `fun w hw => by`.

Establish `hw' : 0 < (w + T).im` using `by simpa using hw`. Rewrite using `[hGw _ hw', hGw _ hw, ← hper ⟨w, hw⟩]`. Use `congr 1`. Use `ext`. Simplify using `[coe_vadd, add_comm]`.

Establish `hint : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..T, G ((t + z.re : ℝ) + y * I) = ∫ x in z.re..z.re + T, G (x + y * I)`. Introduce `y _`. Use `intervalIntegral.integral_comp_add_right (fun x : ℝ => G (x + y * I)) z.re (a := 0) (b := T)` as an intermediate fact. Simplify using `only [zero_add] at this`. Rewrite using `[add_comm z.re T]`.

Conclude with `this`. Establish `hzint : ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = ∫ x in z.re..z.re + T, G (x + z.im * I)`. Rewrite using `[← hint z.im z.im_pos]`. Use `intervalIntegral.integral_congr fun t _ => ?_` and prove the remaining obligations. Establish `him : 0 < (((t + z.re : ℝ) : ℂ) + z.im * I).im` using `by simpa using z.im_pos`.

Rewrite using `[hGw _ him]`. Use `congr 1`. Use `ext`. Simplify using `only [coe_vadd, ofReal_add]`. Rewrite using `[add_assoc]`.

Conclude with `congrArg _ (Complex.re_add_im (z : ℂ)).symm`. Rewrite using `[hzint]`. Use `norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)` and prove the remaining obligations. Rewrite using `[zero_add]`. Take `⟨A, hA⟩` from `(atImInfty_mem _).1 (hzero.eventually (Metric.closedBall_mem_nhds 0 (div_pos hε hT)))`.

Use `set Y := max A 1 + z.im`. Establish `hY : 0 < Y` using `by positivity`. Rewrite using `[integral_periodic_eq_of_im hG hper' z.re z.im_pos hY]`. Establish `hbound : ∀ x ∈ Set.uIoc z.re (z.re + T), ‖G (x + Y * I)‖ ≤ ε / T`. Introduce `x _`.

Establish `him : 0 < ((x : ℂ) + Y * I).im` using `by simpa using hY`. Rewrite using `[hGw _ him]`. Use `hA ⟨_, him⟩ (by show A ≤ ((x : ℂ) + Y * I).im` as an intermediate fact. Simplify using `only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add]`. Use `z.im_pos` as an intermediate fact.

Establish `: A ≤ max A 1` using `le_max_left _ _`. Use the proof step `linarith)`. Simplify `this` using `[Metric.mem_closedBall, dist_zero_right]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_sub_cancel_left, abs_of_pos hT]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem integral_vadd_eq_zero {F : ℍ → ℂ} (hF : MDiff F) {T : ℝ} (hT : 0 < T)
    (hper : ∀ z : ℍ, F (T +ᵥ z) = F z) (hzero : IsZeroAtImInfty F) (z : ℍ) :
    ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = 0 := by
  set G : ℂ → ℂ := F ∘ ofComplex
  have hG : DifferentiableOn ℂ G {w | 0 < w.im} := mdifferentiable_iff.1 hF
  have hGw : ∀ w : ℂ, (hw : 0 < w.im) → G w = F ⟨w, hw⟩ := fun w hw => by
    simp only [G, Function.comp_apply, ofComplex_apply_of_im_pos hw]
  have hper' : ∀ w : ℂ, 0 < w.im → G (w + T) = G w := fun w hw => by
    have hw' : 0 < (w + T).im := by simpa using hw
    rw [hGw _ hw', hGw _ hw, ← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]

  have hint : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..T, G ((t + z.re : ℝ) + y * I) =
      ∫ x in z.re..z.re + T, G (x + y * I) := by
    intro y _
    have := intervalIntegral.integral_comp_add_right (fun x : ℝ => G (x + y * I)) z.re (a := 0) (b := T)
    simp only [zero_add] at this
    rw [add_comm z.re T]
    exact this
  have hzint : ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = ∫ x in z.re..z.re + T, G (x + z.im * I) := by
    rw [← hint z.im z.im_pos]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have him : 0 < (((t + z.re : ℝ) : ℂ) + z.im * I).im := by simpa using z.im_pos
    rw [hGw _ him]
    congr 1
    ext
    simp only [coe_vadd, ofReal_add]
    rw [add_assoc]
    exact congrArg _ (Complex.re_add_im (z : ℂ)).symm
  rw [hzint]

  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (hzero.eventually (Metric.closedBall_mem_nhds 0
    (div_pos hε hT)))
  set Y := max A 1 + z.im
  have hY : 0 < Y := by positivity
  rw [integral_periodic_eq_of_im hG hper' z.re z.im_pos hY]
  have hbound : ∀ x ∈ Set.uIoc z.re (z.re + T), ‖G (x + Y * I)‖ ≤ ε / T := by
    intro x _
    have him : 0 < ((x : ℂ) + Y * I).im := by simpa using hY
    rw [hGw _ him]
    have := hA ⟨_, him⟩ (by
      show A ≤ ((x : ℂ) + Y * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add]
      have := z.im_pos
      have : A ≤ max A 1 := le_max_left _ _
      linarith)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  calc ‖∫ x in z.re..z.re + T, G (x + Y * I)‖ ≤ ε / T * |z.re + T - z.re| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ε := by
        rw [add_sub_cancel_left, abs_of_pos hT]
        field_simp

end GL2Classical

end

end GroundTheory.Automorphic
