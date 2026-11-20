import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `T W _ _ _ l₀ La hadj hpos ⟨v₀, hv₀⟩`. Use `set a : ℂ := ⟪La v₀, l₀ v₀⟫_ℂ with ha`. Use `set n : ℝ := ‖l₀ v₀‖ ^ 2 with hn`. Establish `hnpos : 0 < n` using `by rw [hn]; exact pow_pos (norm_pos_iff.mpr hv₀) 2`. Establish `hnn : ⟪l₀ v₀, l₀ v₀⟫_ℂ = (n : ℂ)`.

Rewrite using `[inner_self_eq_norm_sq_to_K, hn]`. Simplify using the standard rewrite rules. Establish `hnc : (n : ℂ) ≠ 0` using `by exact_mod_cast hnpos.ne'`. Take `⟨him, hre⟩` from `hpos v₀ (l₀ v₀)`. Establish `e : ⟪l₀ v₀, ((innerSL ℂ (La v₀)).smulRight (l₀ v₀)) (l₀ v₀)⟫_ℂ = a * (n : ℂ)`.

Rewrite using `[ContinuousLinearMap.smulRight_apply, inner_smul_right, hnn, innerSL_apply_apply]`. Rewrite `him`, `hre` using `[e]`. Simplify using `only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, sub_zero] at him hre`. Establish `haim : a.im = 0` using `(mul_eq_zero.mp him).resolve_right hnpos.ne'`. Establish `hare : 0 ≤ a.re` using `nonneg_of_mul_nonneg_left hre hnpos`.

Establish `hareal : a = (a.re : ℂ)` using `Complex.ext (by simp) (by simp [haim])`. Use `⟨a.re / n, div_nonneg hare hnpos.le, fun v => ?_⟩` and prove the remaining obligations. Establish `key : (n : ℂ) • La v = a • l₀ v`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `y`.

Establish `h` using `ContinuousLinearMap.adjoint_inner_left ((innerSL ℂ (La v)).smulRight (l₀ v₀)) y (l₀ v₀)`. Rewrite `h` using `[hadj v v₀, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, innerSL_apply_apply, inner_smul_right, hnn, ← ha]`. Rewrite using `[h, inner_smul_left, Complex.conj_ofReal, mul_comm]`. Establish `: La v = (n : ℂ)⁻¹ • ((n : ℂ) • La v)` using `by rw [smul_smul, inv_mul_cancel₀ hnc, one_smul]`. Rewrite using `[this, key, smul_smul]`.

Use `congr 1`. Rewrite using `[Complex.ofReal_div, ← hareal, div_eq_inv_mul]`.
-/
theorem hermitian_rankOne_kernel_shape : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  intro T W _ _ _ l₀ La hadj hpos ⟨v₀, hv₀⟩
  set a : ℂ := ⟪La v₀, l₀ v₀⟫_ℂ with ha
  set n : ℝ := ‖l₀ v₀‖ ^ 2 with hn
  have hnpos : 0 < n := by rw [hn]; exact pow_pos (norm_pos_iff.mpr hv₀) 2
  have hnn : ⟪l₀ v₀, l₀ v₀⟫_ℂ = (n : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hn]; simp
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  obtain ⟨him, hre⟩ := hpos v₀ (l₀ v₀)
  have e : ⟪l₀ v₀, ((innerSL ℂ (La v₀)).smulRight (l₀ v₀)) (l₀ v₀)⟫_ℂ = a * (n : ℂ) := by
    rw [ContinuousLinearMap.smulRight_apply, inner_smul_right, hnn, innerSL_apply_apply]
  rw [e] at him hre
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, sub_zero] at him hre
  have haim : a.im = 0 := (mul_eq_zero.mp him).resolve_right hnpos.ne'
  have hare : 0 ≤ a.re := nonneg_of_mul_nonneg_left hre hnpos
  have hareal : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [haim])
  refine ⟨a.re / n, div_nonneg hare hnpos.le, fun v => ?_⟩
  have key : (n : ℂ) • La v = a • l₀ v := by
    apply ext_inner_right ℂ
    intro y
    have h := ContinuousLinearMap.adjoint_inner_left
      ((innerSL ℂ (La v)).smulRight (l₀ v₀)) y (l₀ v₀)
    rw [hadj v v₀, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, innerSL_apply_apply, inner_smul_right, hnn, ← ha] at h
    rw [h, inner_smul_left, Complex.conj_ofReal, mul_comm]
  have : La v = (n : ℂ)⁻¹ • ((n : ℂ) • La v) := by rw [smul_smul, inv_mul_cancel₀ hnc, one_smul]
  rw [this, key, smul_smul]
  congr 1
  rw [Complex.ofReal_div, ← hareal, div_eq_inv_mul]

end GlobalTheory
