import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Alg

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

/- English proof (translation)
Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_re]`. Conclude with `inner_self_eq_norm_sq (𝕜 := ℂ) a`. Rewrite using `[Complex.ofReal_im]`. Conclude with `inner_self_im (𝕜 := ℂ) a`.
-/
theorem inner_self_cast (a : Wp) : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) a
  · rw [Complex.ofReal_im]
    exact inner_self_im (𝕜 := ℂ) a

/- English proof (translation)
Establish `hinner : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ)` using `inner_self_cast a`. Establish `hnq : ‖⟪a, a⟫_ℂ‖ = ‖a‖ ^ 2`. Rewrite using `[hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Establish `hc : (‖⟪a, a⟫_ℂ‖₊ : ENNReal) = ENNReal.ofReal (‖a‖ ^ 2)`. Rewrite using `[← hnq]`.

Conclude with `(ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm`. Establish `hT : PI.BesselPeriodGGP.l2SG (k` using `k) (r := r) νq T = ENNReal.ofReal (‖a‖ ^ 2) ^ 2 * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F := by`. Unfold `PI.BesselPeriodGGP.l2SG`. Rewrite using `[← lintegral_const_mul' (ENNReal.ofReal (‖a‖ ^ 2) ^ 2) _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]`. Use `lintegral_congr_ae (hae.mono fun x hx => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, hc]`. Establish `hre : (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re = ‖a‖ ^ 4`. Rewrite using `[inner_smul_right, hinner, ← Complex.ofReal_mul, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hN` using `[hT, hre]`. Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Simplify using the standard rewrite rules. Establish `hp : 0 < ‖a‖ ^ 2` using `pow_pos (norm_pos_iff.mpr ha) 2`. Establish `key : ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k` using `k) (r := r) νq F) = ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by`.

Rewrite using `[← mul_assoc, ← pow_two, hN, ← ENNReal.ofReal_mul hp.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp key`.
-/
theorem l2_norm_scaling {νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (T F : Mx k r → Wp) (a : Wp) (U D : ℝ) (hU : 0 ≤ U)
    (hN : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (U * (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re / D))
    (hae : ∀ᵐ x ∂νq, T (Matrix.of x) = ⟪a, a⟫_ℂ • F (Matrix.of x)) :
    ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F =
      ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
  have hinner : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := inner_self_cast a
  have hnq : ‖⟪a, a⟫_ℂ‖ = ‖a‖ ^ 2 := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : (‖⟪a, a⟫_ℂ‖₊ : ENNReal) = ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [← hnq]
    exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
  have hT : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (‖a‖ ^ 2) ^ 2 * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' (ENNReal.ofReal (‖a‖ ^ 2) ^ 2) _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    dsimp only
    rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, hc]
  have hre : (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re = ‖a‖ ^ 4 := by
    rw [inner_smul_right, hinner, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hT, hre] at hN
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hp : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have key : ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F) =
      ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
    rw [← mul_assoc, ← pow_two, hN, ← ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp key

end Alg

/- English proof (translation)
Introduce `hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hnz`. Establish `hS'` using `hS`. Take `⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩` from `hS'`. Establish `hsm` using `DD_smooth hIn.2.2.1 hlam hσ hw0`. Take `⟨-, -, -, hBC4⟩` from `hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS`.

Take `⟨x0, hx0, y0, hy0, hne⟩` from `hnz`. Choose the witnesses or unpack the hypotheses as in `⟨ξ0, hξ0⟩ : ∃ ξ, be z c π σ μW μN x0 y0 ξ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hne (ContinuousLinearMap.ext hcon)`.

Establish `hB0` using `hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) ξ0`. Use `set B0 : H → Wp := fun x => be z c π σ μW μN x y0 ξ0 with hB0def`. Establish `hB0x : B0 x0 ≠ 0` using `hξ0`. Establish `hcoef : ∀ v ∈ DDsp σ w0, ∀ ξ : Wp, ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ, be z c π σ μW μN x v ξ = κ • B0 x := fun v hv ξ => jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hB0 (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inl hv) ξ) (hsm x0 hx0) hB0x`. Use `choose! cf hcf using hcoef`.

Establish `herm : ∀ x ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, ∀ η ξ : Wp, cf v ξ * ⟪η, B0 x⟫_ℂ = conj (cf x η) * ⟪B0 v, ξ⟫_ℂ`. Introduce `x hx v hv η ξ`. Establish `hadj` using `(hBC4 x hx v (Or.inl hv)).2`. Establish `e` using `ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x v) ξ η`. Rewrite `e` using `[hadj, hcf v hv ξ x (hsm x hx), hcf x hx η v (hsm v hv), inner_smul_left, inner_smul_right]`.

Conclude with `e.symm`. Establish `hη : ⟪B0 x0, B0 x0⟫_ℂ ≠ 0` using `inner_self_ne_zero.mpr hB0x`. Use `set κ : ℂ := conj (cf x0 (B0 x0)) / ⟪B0 x0, B0 x0⟫_ℂ with hκdef`. Establish `hcf' : ∀ v ∈ DDsp σ w0, ∀ ξ, cf v ξ = κ * ⟪B0 v, ξ⟫_ℂ`. Introduce `v hv ξ`.

Establish `e` using `herm x0 hx0 v hv (B0 x0) ξ`. Rewrite using `[hκdef, div_mul_eq_mul_div, eq_div_iff hη]`. Take the linear combination `e`. Establish `hform : ∀ x ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ, ∀ v ∈ DDsp σ w0, ∀ ξ, be z c π σ μW μN x v ξ = (κ * ⟪B0 v, ξ⟫_ℂ) • B0 x := fun x hx v hv ξ => by`. Rewrite using `[hcf v hv ξ x hx, hcf' v hv ξ]`.

Establish `hκ0 : κ ≠ 0`. Introduce `h0`. Apply `hξ0` to reduce the goal to its premises. Use `show be z c π σ μW μN x0 y0 ξ0 = 0`. Rewrite using `[hform x0 (hsm x0 hx0) y0 hy0 ξ0, h0, zero_mul, zero_smul]`.

Establish `hpos` using `(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x0 (hsm x0 hx0) x0 (Or.inl hx0) (B0 x0)).2`. Rewrite `hpos` using `[hform x0 (hsm x0 hx0) x0 hx0, inner_smul_right, inner_self_cast]`. Use `set N2 : ℝ := ‖B0 x0‖ ^ 2 with hN2`. Establish `hN2pos : 0 < N2` using `by rw [hN2]; have := norm_pos_iff.mpr hB0x; positivity`. Establish `hexp : κ * (N2 : ℂ) * (N2 : ℂ) = κ * ((N2 * N2 : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite `hpos` using `[hexp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]`. Simplify using `only [mul_zero, zero_add, sub_zero] at hpos`. Establish `hNN : 0 < N2 * N2` using `mul_pos hN2pos hN2pos`. Establish `him : κ.im = 0`. Break down `mul_eq_zero.mp hpos.1 with h1 | h1` into its components or cases.

Conclude with `h1`. Conclude with `absurd h1 hNN.ne'`. Establish `hre0 : 0 ≤ κ.re`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Establish `: κ.re * (N2 * N2) < 0` using `mul_neg_of_neg_of_pos hneg hNN`. Combine the linear relations using `[hpos.2]`. Establish `hre : 0 < κ.re`. Break down `hre0.lt_or_eq with h1 | h1` into its components or cases. Conclude with `h1`.

Conclude with `absurd (Complex.ext (by simp [← h1]) (by simp [him])) hκ0`. Use `set s : ℝ := Real.sqrt κ.re with hs`. Establish `hss : (s : ℂ) * (s : ℂ) = κ`. Rewrite using `[← Complex.ofReal_mul, hs, Real.mul_self_sqrt hre.le]`. Conclude with `Complex.ext (by simp) (by simp [him])`.

Establish `hspos : 0 < s` using `Real.sqrt_pos.mpr hre`. Use `⟨fun x => (s : ℂ) • B0 x, bessel_smul hB0 _, ⟨x0, hx0, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `smul_ne_zero (by exact_mod_cast hspos.ne') hB0x`. Introduce `x hx v hv`. Use extensionality with `ξ`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`. Rewrite using `[hform x hx v hv ξ, inner_smul_left, Complex.conj_ofReal, smul_smul]`. Use `congr 1`. Rewrite using `[← hss]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shape_of (hPsi : PsiConst) (hSch : SchurH) (hBC : BeConv) (hNI : NormIdSm) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hnz
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨x0, hx0, y0, hy0, hne⟩ := hnz
  obtain ⟨ξ0, hξ0⟩ : ∃ ξ, be z c π σ μW μN x0 y0 ξ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB0 := hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) ξ0
  set B0 : H → Wp := fun x => be z c π σ μW μN x y0 ξ0 with hB0def
  have hB0x : B0 x0 ≠ 0 := hξ0
  have hcoef : ∀ v ∈ DDsp σ w0, ∀ ξ : Wp, ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v ξ = κ • B0 x := fun v hv ξ =>
    jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hB0
      (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inl hv) ξ) (hsm x0 hx0) hB0x
  choose! cf hcf using hcoef
  have herm : ∀ x ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, ∀ η ξ : Wp,
      cf v ξ * ⟪η, B0 x⟫_ℂ = conj (cf x η) * ⟪B0 v, ξ⟫_ℂ := by
    intro x hx v hv η ξ
    have hadj := (hBC4 x hx v (Or.inl hv)).2
    have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x v) ξ η
    rw [hadj, hcf v hv ξ x (hsm x hx), hcf x hx η v (hsm v hv), inner_smul_left, inner_smul_right] at e
    exact e.symm
  have hη : ⟪B0 x0, B0 x0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hB0x
  set κ : ℂ := conj (cf x0 (B0 x0)) / ⟪B0 x0, B0 x0⟫_ℂ with hκdef
  have hcf' : ∀ v ∈ DDsp σ w0, ∀ ξ, cf v ξ = κ * ⟪B0 v, ξ⟫_ℂ := by
    intro v hv ξ
    have e := herm x0 hx0 v hv (B0 x0) ξ
    rw [hκdef, div_mul_eq_mul_div, eq_div_iff hη]
    linear_combination e
  have hform : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, ∀ ξ,
      be z c π σ μW μN x v ξ = (κ * ⟪B0 v, ξ⟫_ℂ) • B0 x := fun x hx v hv ξ => by
    rw [hcf v hv ξ x hx, hcf' v hv ξ]
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hξ0
    show be z c π σ μW μN x0 y0 ξ0 = 0
    rw [hform x0 (hsm x0 hx0) y0 hy0 ξ0, h0, zero_mul, zero_smul]
  have hpos := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x0 (hsm x0 hx0) x0 (Or.inl hx0)
    (B0 x0)).2
  rw [hform x0 (hsm x0 hx0) x0 hx0, inner_smul_right, inner_self_cast] at hpos
  set N2 : ℝ := ‖B0 x0‖ ^ 2 with hN2
  have hN2pos : 0 < N2 := by rw [hN2]; have := norm_pos_iff.mpr hB0x; positivity
  have hexp : κ * (N2 : ℂ) * (N2 : ℂ) = κ * ((N2 * N2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hpos
  simp only [mul_zero, zero_add, sub_zero] at hpos
  have hNN : 0 < N2 * N2 := mul_pos hN2pos hN2pos
  have him : κ.im = 0 := by
    rcases mul_eq_zero.mp hpos.1 with h1 | h1
    · exact h1
    · exact absurd h1 hNN.ne'
  have hre0 : 0 ≤ κ.re := by
    by_contra hneg; push_neg at hneg
    have : κ.re * (N2 * N2) < 0 := mul_neg_of_neg_of_pos hneg hNN
    linarith [hpos.2]
  have hre : 0 < κ.re := by
    rcases hre0.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (Complex.ext (by simp [← h1]) (by simp [him])) hκ0
  set s : ℝ := Real.sqrt κ.re with hs
  have hss : (s : ℂ) * (s : ℂ) = κ := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hre.le]
    exact Complex.ext (by simp) (by simp [him])
  have hspos : 0 < s := Real.sqrt_pos.mpr hre
  refine ⟨fun x => (s : ℂ) • B0 x, bessel_smul hB0 _, ⟨x0, hx0, ?_⟩, ?_⟩
  · exact smul_ne_zero (by exact_mod_cast hspos.ne') hB0x
  · intro x hx v hv
    ext ξ
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hform x hx v hv ξ, inner_smul_left, Complex.conj_ofReal, smul_smul]
    congr 1
    rw [← hss]; ring

/- English proof (translation)
Introduce `hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl hx1e hid v hv x hx`. Take `⟨x1, hx1, hlx1⟩` from `hx1e`. Establish `hS'` using `hS`. Take `⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩` from `hS'`. Establish `hsm` using `DD_smooth hIn.2.2.1 hlam hσ hw0`.

Establish `hvs : v ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv`. Take `⟨-, -, -, hBC4⟩` from `hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS`. Use extensionality with `ξ`. Take `⟨κ, hκ⟩` from `jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hl (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ) (hsm x1 hx1) hlx1`. Establish `hadj` using `(hBC4 x1 hx1 v (Or.inr hv)).2`.

Establish `e` using `ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x1 v) ξ (l x1)`. Rewrite `e` using `[hadj, hκ x1 (hsm x1 hx1), hid v hvs x1 hx1]`. Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right, inner_conj_symm] at e`. Establish `hn : ⟪l x1, l x1⟫_ℂ ≠ 0` using `inner_self_ne_zero.mpr hlx1`. Establish `hκv : κ = ⟪l v, ξ⟫_ℂ`.

Apply `mul_left_cancel₀ hn` to reduce the goal to its premises. Take the linear combination `-e`. Rewrite using `[hκ x hx, hκv]`. Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`.
-/
theorem kFinForm_of (hPsi : PsiConst) (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl hx1e hid v hv x hx
  obtain ⟨x1, hx1, hlx1⟩ := hx1e
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  obtain ⟨κ, hκ⟩ := jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hl
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ) (hsm x1 hx1) hlx1
  have hadj := (hBC4 x1 hx1 v (Or.inr hv)).2
  have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x1 v) ξ (l x1)
  rw [hadj, hκ x1 (hsm x1 hx1), hid v hvs x1 hx1] at e
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm] at e
  have hn : ⟪l x1, l x1⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hlx1
  have hκv : κ = ⟪l v, ξ⟫_ℂ := by
    apply mul_left_cancel₀ hn
    linear_combination -e
  rw [hκ x hx, hκv]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/- English proof (translation)
Introduce `hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS`. Establish `hS'` using `hS`. Take `⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩` from `hS'`. Establish `hsm` using `DD_smooth hIn.2.2.1 hlam hσ hw0`. Take `⟨hBC1, -, -, -⟩` from `hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS`.

Take `⟨d, hd, hSd⟩` from `hSch k r ε lam H σ μG hlam hσ hG`. Establish `hw0n : w0 ≠ 0`. Take `⟨P, -, hn1, -⟩` from `hw0`. Introduce `h0`. Rewrite `hn1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one hn1`. Establish `hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d` using `fun x hx => fdeg_eq hd hSd hx`. Establish `hmu` using `muSof_facts hW hN`. Establish `hae` using `ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq`. Distinguish the cases in `hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0`.

Take `⟨l, hl, -, hid⟩` from `hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz`. Use `⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx hx0 v hv`. Establish `hNv` using `(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1`. Rewrite `hNv` using `[hid v (hsm v hv) v hv]`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv`. Rewrite `hNv` using `[hdeg w0 hw0n]`. Rewrite using `[hdeg x hx0]`. Use `l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)` and prove the remaining obligations. Rewrite using `[hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`. Use `push_neg at hnz`. Use `⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩, fun x _ _ v _ => by simp⟩` and prove the remaining obligations. Use `show be z c π σ μW μN x v = _`. Rewrite using `[hnz x hx v hv]`.

Use extensionality with `ξ`. Simplify using the standard rewrite rules.
-/
theorem discrete_form_one_side : DDFormOneOfSteps := by
  intro hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, -, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1
    rw [hid v (hsm v hv) v hv] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [hnz x hx v hv]
    ext ξ; simp

end Formalism.FourierDecayAlt.P.DDSmoothness
