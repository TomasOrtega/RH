import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadPictureEmptyWord

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section wirt1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dz (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 - Complex.I • fderiv ℝ f τ Complex.I)

def dzb (f : ℂ → E) (τ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I)

/- English proof (translation)
Establish `h2 : HasFDerivAt (fun σ : ℂ => ‖σ‖ ^ 2) (2 • innerSL ℝ τ) τ` using `(hasStrictFDerivAt_norm_sq τ).hasFDerivAt`. Establish `h1` using `h2.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 hτ))`. Establish `e : (fun σ : ℂ => Real.sqrt (‖σ‖ ^ 2)) = fun σ => ‖σ‖` using `funext fun σ => Real.sqrt_sq (norm_nonneg σ)`. Rewrite `h1` using `[e]`. Conclude with `h1`.
-/
theorem hasFDerivAt_norm1 {τ : ℂ} (hτ : τ ≠ 0) :
    HasFDerivAt (fun σ : ℂ => ‖σ‖) ((1 / (2 * Real.sqrt (‖τ‖ ^ 2))) • (2 • innerSL ℝ τ)) τ := by
  have h2 : HasFDerivAt (fun σ : ℂ => ‖σ‖ ^ 2) (2 • innerSL ℝ τ) τ := (hasStrictFDerivAt_norm_sq τ).hasFDerivAt
  have h1 := h2.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 hτ))
  have e : (fun σ : ℂ => Real.sqrt (‖σ‖ ^ 2)) = fun σ => ‖σ‖ := funext fun σ => Real.sqrt_sq (norm_nonneg σ)
  rw [e] at h1
  exact h1

/- English proof (translation)
Rewrite using `[(hasFDerivAt_norm1 hτ).fderiv]`. Establish `hs : Real.sqrt (‖τ‖ ^ 2) = ‖τ‖` using `Real.sqrt_sq (norm_nonneg τ)`. Simplify using `only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, hs, smul_eq_mul, Complex.inner, nsmul_eq_mul]`. Establish `hn : ‖τ‖ ≠ 0` using `norm_ne_zero_iff.2 hτ`. Simplify using `only [Complex.conj_re, Complex.conj_im, Complex.mul_re]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_norm_apply {τ : ℂ} (hτ : τ ≠ 0) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖) τ v = ‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im) := by
  rw [(hasFDerivAt_norm1 hτ).fderiv]
  have hs : Real.sqrt (‖τ‖ ^ 2) = ‖τ‖ := Real.sqrt_sq (norm_nonneg τ)
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, hs, smul_eq_mul, Complex.inner, nsmul_eq_mul]
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re]
  field_simp
  ring

/- English proof (translation)
Rewrite using `[((hasFDerivAt_norm1 hτ).pow n).fderiv]`. Rewrite using `[← (hasFDerivAt_norm1 hτ).fderiv]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, fderiv_norm_apply hτ]`.
-/
theorem normPow_deriv_apply {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) (v : ℂ) :
    fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ v =
      (n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * (τ.re * v.re + τ.im * v.im)) := by
  rw [((hasFDerivAt_norm1 hτ).pow n).fderiv]
  rw [← (hasFDerivAt_norm1 hτ).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, fderiv_norm_apply hτ]

/- English proof (translation)
Establish `hn : ‖τ‖ ≠ 0` using `norm_ne_zero_iff.2 hτ`. Establish `hconj : τ * ((τ.re : ℂ) - Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ)`. Use `Complex.mul_conj τ` as an intermediate fact. Rewrite `this` using `[Complex.normSq_eq_norm_sq]`. Rewrite using `[← this]`.

Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`. Break down `n with _ | m` into its components or cases. Simplify using the standard rewrite rules. Establish `e : τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) - Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) = (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (τ * ((τ.re : ℂ) - Complex.I * τ.im))`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hconj]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauge_scalar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) -
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : τ * ((τ.re : ℂ) - Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) -
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (τ * ((τ.re : ℂ) - Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

/- English proof (translation)
Establish `hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ` using `Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt`. Establish `hP` using `hN.smul hf.hasFDerivAt`. Establish `hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f` using `rfl`. Unfold `dz`. Rewrite using `[hfun, hP.fderiv]`.

Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]`. Establish `key` using `gauge_scalar hτ n`. Simplify using `only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *`. Take the linear combination `(norm := module) key • f τ`.
-/
theorem dz_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    τ • dz (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (τ • dz f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dz
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

/- English proof (translation)
Establish `hn : ‖τ‖ ≠ 0` using `norm_ne_zero_iff.2 hτ`. Establish `hconj : conj τ * ((τ.re : ℂ) + Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ)`. Use `Complex.mul_conj τ` as an intermediate fact. Rewrite `this` using `[Complex.normSq_eq_norm_sq, mul_comm]`. Rewrite using `[← this]`.

Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`. Break down `n with _ | m` into its components or cases. Simplify using the standard rewrite rules. Establish `e : conj τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) + Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) = (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (conj τ * ((τ.re : ℂ) + Complex.I * τ.im))`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hconj]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauge_scalar_bar {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) :
    conj τ * (1 / 2) * ((((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ) +
        Complex.I * (((n : ℝ) * ‖τ‖ ^ (n - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
      ((‖τ‖ ^ n : ℝ) : ℂ) * ((n : ℂ) / 2) := by
  have hn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
  have hconj : conj τ * ((τ.re : ℂ) + Complex.I * τ.im) = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
    have := Complex.mul_conj τ
    rw [Complex.normSq_eq_norm_sq, mul_comm] at this
    rw [← this]
    congr 1
    apply Complex.ext <;> simp
  rcases n with _ | m
  · simp
  · have e : conj τ * (1 / 2) * ((((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.re) : ℝ) : ℂ)) +
        Complex.I * ((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ (m + 1 - 1) * (‖τ‖⁻¹ * τ.im) : ℝ) : ℂ)) =
        (((((m + 1 : ℕ) : ℝ) * ‖τ‖ ^ m * ‖τ‖⁻¹ / 2 : ℝ) : ℂ)) * (conj τ * ((τ.re : ℂ) + Complex.I * τ.im)) := by
      push_cast
      ring
    rw [e, hconj]
    push_cast
    field_simp
    ring

/- English proof (translation)
Establish `hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ` using `Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt`. Establish `hP` using `hN.smul hf.hasFDerivAt`. Establish `hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f` using `rfl`. Unfold `dzb`. Rewrite using `[hfun, hP.fderiv]`.

Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]`. Establish `key` using `gauge_scalar_bar hτ n`. Simplify using `only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *`. Take the linear combination `(norm := module) key • f τ`.
-/
theorem dzb_gauge {τ : ℂ} (hτ : τ ≠ 0) (n : ℕ) {f : ℂ → E} (hf : DifferentiableAt ℝ f τ) :
    conj τ • dzb (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) τ =
      ((‖τ‖ ^ n : ℝ) : ℂ) • (conj τ • dzb f τ + ((n : ℂ) / 2) • f τ) := by
  have hN : HasFDerivAt (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun σ : ℂ => ‖σ‖ ^ n) τ)) τ :=
    Complex.ofRealCLM.hasFDerivAt.comp τ ((hasFDerivAt_norm1 hτ).pow n).differentiableAt.hasFDerivAt
  have hP := hN.smul hf.hasFDerivAt
  have hfun : (fun σ => ((‖σ‖ ^ n : ℝ) : ℂ) • f σ) = (fun σ : ℂ => ((‖σ‖ ^ n : ℝ) : ℂ)) • f := rfl
  unfold dzb
  rw [hfun, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, normPow_deriv_apply hτ]
  have key := gauge_scalar_bar hτ n
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at *
  linear_combination (norm := module) key • f τ

end wirt1

section read0

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pt0 {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) : Fin n → ℂ := fun l => PBH.consC τ c (Fin.cast hn.symm l)

def Lz {n : ℕ} : ℂ →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun l : Fin n => if l.val = 0 then ContinuousLinearMap.id ℝ ℂ else 0

/- English proof (translation)
Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l.val = 0`. Establish `: l = ⟨0, h0⟩` using `Fin.ext hl`. Substitute `this` using the available equality. Simplify using `[Lz]`.

Establish `: l ≠ ⟨0, h0⟩` using `fun h => hl (by rw [h])`. Simplify using `[Lz, hl, this]`.
-/
theorem Lz_apply {n : ℕ} (h0 : 0 < n) (v : ℂ) : (Lz (n := n)) v = Pi.single ⟨0, h0⟩ v := by
  funext l
  by_cases hl : l.val = 0
  · have : l = ⟨0, h0⟩ := Fin.ext hl
    subst this
    simp [Lz]
  · have : l ≠ ⟨0, h0⟩ := fun h => hl (by rw [h])
    simp [Lz, hl, this]

/- English proof (translation)
Establish `e : pt0 hn c = fun σ => Lz (n` using `n) σ + pt0 hn c 0 := by`. Use function extensionality and compare the values at `σ l`. Use `show PBH.consC σ c (Fin.cast hn.symm l) = (Lz (n := n)) σ l + PBH.consC 0 c (Fin.cast hn.symm l)`. Distinguish the cases in `hl : l.val = 0`. Simplify using `[PBH.consC, Lz, hl]`.

Simplify using `[PBH.consC, Lz, hl]`. Rewrite using `[e]`. Conclude with `(Lz (n := n)).hasFDerivAt.add_const _`.
-/
theorem hasFDerivAt_base_point {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    HasFDerivAt (pt0 hn c) (Lz (n := n)) τ := by
  have e : pt0 hn c = fun σ => Lz (n := n) σ + pt0 hn c 0 := by
    funext σ l
    show PBH.consC σ c (Fin.cast hn.symm l) = (Lz (n := n)) σ l + PBH.consC 0 c (Fin.cast hn.symm l)
    by_cases hl : l.val = 0
    · simp [PBH.consC, Lz, hl]
    · simp [PBH.consC, Lz, hl]
  rw [e]
  exact (Lz (n := n)).hasFDerivAt.add_const _

/- English proof (translation)
Simplify using `[pt0, PBH.consC]`.
-/
theorem base_point_zero_coord {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin ρ → ℂ) (τ : ℂ) :
    pt0 hn c τ ⟨0, by omega⟩ = τ := by
  simp [pt0, PBH.consC]

/- English proof (translation)
Substitute `hn` using the available equality. Establish `e : pt0 rfl c τ = PBH.consC τ c` using `funext fun l => by simp [pt0]`. Rewrite using `[e]`. Conclude with `(PBH.omX_consC hτ c).2 hc`.
-/
theorem pointWithZeroSecondCoord_mem_chart_of_restricted {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0) :
    pt0 hn c τ ∈ OmX n := by
  subst hn
  have e : pt0 rfl c τ = PBH.consC τ c := funext fun l => by simp [pt0]
  rw [e]
  exact (PBH.omX_consC hτ c).2 hc

/- English proof (translation)
Establish `hmem` using `pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ`. Establish `h0` using `base_point_zero_coord hn c τ`. Establish `hd : ∀ v, fderiv ℝ (fun σ => f (pt0 hn c σ)) τ v = fderiv ℝ f (pt0 hn c τ) (Pi.single ⟨0, by omega⟩ v)`. Introduce `v`. Establish `h` using `(hf.hasFDerivAt.comp τ (hasFDerivAt_base_point hn c τ)).fderiv`.

Express the relevant statement in the definitionally equal form `fderiv ℝ (f ∘ pt0 hn c) τ v = _`. Rewrite using `[h, ContinuousLinearMap.comp_apply, Lz_apply]`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show pOp _ f _ = _`. Unfold `pOp`.

Rewrite using `[if_pos hmem, h0]`. Unfold `wirt dz`. Rewrite using `[hd, hd]`. Use `show cOp _ f _ = _`. Simplify using `only [cOp, h0]`.

Use `show ciOp _ f _ = _`. Simplify using `only [ciOp, h0]`. Use `show pbOp _ f _ = _`. Unfold `pbOp`. Rewrite using `[if_pos hmem, h0]`.

Unfold `wirtBar dzb`. Rewrite using `[hd, hd]`. Both sides reduce to the same expression. Use `show cbOp _ f _ = _`. Simplify using `only [cbOp, h0]`.

Both sides reduce to the same expression. Use `show cbiOp _ f _ = _`. Simplify using `only [cbiOp, h0]`. Both sides reduce to the same expression.
-/
theorem operators_at_base_point {n ρ : ℕ} (hn : 1 + ρ = n) {c : Fin ρ → ℂ} (hc : c ∈ OmX ρ) {τ : ℂ} (hτ : τ ≠ 0)
    (f : (Fin n → ℂ) → E) (hf : DifferentiableAt ℝ f (pt0 hn c τ)) :
    opL (⟨0, by omega⟩ : Fin n) 0 f (pt0 hn c τ) = τ • dz (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 1 f (pt0 hn c τ) = τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 2 f (pt0 hn c τ) = τ⁻¹ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 3 f (pt0 hn c τ) = conj τ • dzb (fun σ => f (pt0 hn c σ)) τ ∧
    opL (⟨0, by omega⟩ : Fin n) 4 f (pt0 hn c τ) = conj τ • f (pt0 hn c τ) ∧
    opL (⟨0, by omega⟩ : Fin n) 5 f (pt0 hn c τ) = (conj τ)⁻¹ • f (pt0 hn c τ) := by
  have hmem := pointWithZeroSecondCoord_mem_chart_of_restricted hn hc hτ
  have h0 := base_point_zero_coord hn c τ
  have hd : ∀ v, fderiv ℝ (fun σ => f (pt0 hn c σ)) τ v = fderiv ℝ f (pt0 hn c τ) (Pi.single ⟨0, by omega⟩ v) := by
    intro v
    have h := (hf.hasFDerivAt.comp τ (hasFDerivAt_base_point hn c τ)).fderiv
    change fderiv ℝ (f ∘ pt0 hn c) τ v = _
    rw [h, ContinuousLinearMap.comp_apply, Lz_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show pOp _ f _ = _
    unfold pOp
    rw [if_pos hmem, h0]
    unfold wirt dz
    rw [hd, hd]
  · show cOp _ f _ = _
    simp only [cOp, h0]
  · show ciOp _ f _ = _
    simp only [ciOp, h0]
  · show pbOp _ f _ = _
    unfold pbOp
    rw [if_pos hmem, h0]
    unfold wirtBar dzb
    rw [hd, hd]
    rfl
  · show cbOp _ f _ = _
    simp only [cbOp, h0]
    rfl
  · show cbiOp _ f _ = _
    simp only [cbiOp, h0]
    rfl

end read0

end Formalism.FourierDecayAlt.P.PBP
