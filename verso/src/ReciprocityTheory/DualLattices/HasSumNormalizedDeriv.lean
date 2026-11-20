import Mathlib

open UpperHalfPlane hiding I
open Complex Filter Function
open scoped Real Manifold Topology

namespace ReciprocityTheory.PGsh

local notation "𝕢" => Periodic.qParam

/- English proof (translation)
Rewrite using `[Periodic.qParam, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qParam_one_pow_eq_cexp (z : ℂ) (m : ℕ) :
    𝕢 1 z ^ m = cexp (2 * π * I * m * z) := by
  rw [Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Use `set y0 : ℝ := τ.im / 2 with hy0`. Establish `hy0pos : 0 < y0` using `by have := τ.im_pos; positivity`. Establish `hy0lt : y0 < τ.im` using `by have := τ.im_pos; rw [hy0]; linarith`. Set `τ0 : ℍ` to `⟨(y0 : ℂ) * I, by simpa using hy0pos⟩`. Establish `hτ0im : (τ0 : ℂ).im = y0` using `by simp [τ0]`.

Use `set r : ℝ := ‖𝕢 1 (τ0 : ℂ)‖ with hr`. Establish `hsum : Summable (fun m : ℕ ↦ ‖c m‖ * r ^ m)`. Use `(hF τ0).summable.norm` as an intermediate fact. Use `this.congr fun m ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_pow]`.

Use `set U : Set ℂ := {z : ℂ | y0 < z.im} with hU`. Establish `hUo : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_im`. Establish `hτU : (τ : ℂ) ∈ U` using `by simpa [hU] using hy0lt`. Set `G : ℕ → ℂ → ℂ` to `fun m z ↦ c m * cexp (2 * π * I * m * z)`. Establish `hGd : ∀ m, DifferentiableOn ℂ (G m) U` using `fun m ↦ by`.

Introduce `z _`. Conclude with `(by fun_prop : Differentiable ℂ (G m)).differentiableAt.differentiableWithinAt`. Establish `hGle : ∀ m (z : ℂ), z ∈ U → ‖G m z‖ ≤ ‖c m‖ * r ^ m`. Introduce `m z hz`. Simplify using `only [G, norm_mul, ← qParam_one_pow_eq_cexp, norm_pow]`.

Use `gcongr`. Rewrite using `[hr, Periodic.norm_qParam, Periodic.norm_qParam, Real.exp_le_exp, hτ0im]`. Establish `: y0 < z.im` using `hz`. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hmain` using `hasSum_deriv_of_summable_norm hsum hGd hUo hGle hτU`. Establish `heq : (fun w : ℂ ↦ ∑' m, G m w) =ᶠ[𝓝 (τ : ℂ)] F ∘ ofComplex` using `by filter_upwards [hUo.mem_nhds hτU] with w hw`. Establish `hw0 : 0 < w.im` using `lt_trans hy0pos hw`. Simplify using `only [comp_apply, ofComplex_apply_of_im_pos hw0]`. Rewrite using `[← (hF ⟨w, hw0⟩).tsum_eq]`.

Use `tsum_congr fun m ↦ ?_` and prove the remaining obligations. Simplify using `[G, qParam_one_pow_eq_cexp]`. Rewrite `hmain` using `[heq.deriv_eq]`. Establish `hderiv : ∀ m, deriv (G m) τ = 2 * π * I * m * (c m * cexp (2 * π * I * m * τ))`. Introduce `m`.

Establish `h1 : HasDerivAt (fun z : ℂ ↦ 2 * π * I * m * z) (2 * π * I * m) (τ : ℂ)`. Simplify using `using (hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I * m)`. Establish `h2` using `(h1.cexp).const_mul (c m)`. Rewrite using `[h2.deriv]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hderiv] at hmain`. Establish `hfin` using `hmain.mul_left (2 * π * I)⁻¹`. Unfold `Derivative.normalizedDerivOfComplex`. Establish `h2pi : (2 * π * I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, I_ne_zero]`.

Use `hfin.congr_fun fun m ↦ ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, qParam_one_pow_eq_cexp]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasSum_normalizedDeriv {F : ℍ → ℂ} {c : ℕ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 τ ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ((m : ℂ) * c m) • 𝕢 1 τ ^ m)
      (Derivative.normalizedDerivOfComplex F τ) := by
  set y0 : ℝ := τ.im / 2 with hy0
  have hy0pos : 0 < y0 := by have := τ.im_pos; positivity
  have hy0lt : y0 < τ.im := by have := τ.im_pos; rw [hy0]; linarith
  let τ0 : ℍ := ⟨(y0 : ℂ) * I, by simpa using hy0pos⟩
  have hτ0im : (τ0 : ℂ).im = y0 := by simp [τ0]
  set r : ℝ := ‖𝕢 1 (τ0 : ℂ)‖ with hr
  have hsum : Summable (fun m : ℕ ↦ ‖c m‖ * r ^ m) := by
    have := (hF τ0).summable.norm
    refine this.congr fun m ↦ ?_
    rw [norm_smul, norm_pow]
  set U : Set ℂ := {z : ℂ | y0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ U := by simpa [hU] using hy0lt
  let G : ℕ → ℂ → ℂ := fun m z ↦ c m * cexp (2 * π * I * m * z)
  have hGd : ∀ m, DifferentiableOn ℂ (G m) U := fun m ↦ by
    intro z _
    exact (by fun_prop : Differentiable ℂ (G m)).differentiableAt.differentiableWithinAt
  have hGle : ∀ m (z : ℂ), z ∈ U → ‖G m z‖ ≤ ‖c m‖ * r ^ m := by
    intro m z hz
    simp only [G, norm_mul, ← qParam_one_pow_eq_cexp, norm_pow]
    gcongr
    rw [hr, Periodic.norm_qParam, Periodic.norm_qParam, Real.exp_le_exp, hτ0im]
    have : y0 < z.im := hz
    have := Real.pi_pos
    nlinarith
  have hmain := hasSum_deriv_of_summable_norm hsum hGd hUo hGle hτU
  have heq : (fun w : ℂ ↦ ∑' m, G m w) =ᶠ[𝓝 (τ : ℂ)] F ∘ ofComplex := by
    filter_upwards [hUo.mem_nhds hτU] with w hw
    have hw0 : 0 < w.im := lt_trans hy0pos hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw0]
    rw [← (hF ⟨w, hw0⟩).tsum_eq]
    refine tsum_congr fun m ↦ ?_
    simp [G, qParam_one_pow_eq_cexp]
  rw [heq.deriv_eq] at hmain
  have hderiv : ∀ m, deriv (G m) τ = 2 * π * I * m * (c m * cexp (2 * π * I * m * τ)) := by
    intro m
    have h1 : HasDerivAt (fun z : ℂ ↦ 2 * π * I * m * z) (2 * π * I * m) (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I * m)
    have h2 := (h1.cexp).const_mul (c m)
    rw [h2.deriv]
    ring
  simp only [hderiv] at hmain
  have hfin := hmain.mul_left (2 * π * I)⁻¹
  unfold Derivative.normalizedDerivOfComplex
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  refine hfin.congr_fun fun m ↦ ?_
  rw [smul_eq_mul, qParam_one_pow_eq_cexp]
  field_simp

end ReciprocityTheory.PGsh
