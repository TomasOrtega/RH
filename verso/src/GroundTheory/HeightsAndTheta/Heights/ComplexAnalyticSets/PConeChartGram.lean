import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSheetGram
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeChartArea
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

noncomputable section

/- English proof (translation)
Take `⟨B, hB⟩` from `(isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn (hc.mono fun x hx => by`. Introduce and unpack `rfl`. Simplify using `at hx)`. Use `⟨max B |g 0|, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Conclude with `le_max_right _ _`. Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.2 hx`. Establish `hne : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0` using `by simpa using hn`. Rewrite using `[← hdeg _ x hne]`.

Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations. Establish `hmem : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ sphere (0 : Fin n → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]`. Simplify `hB _ hmem` using `[Real.norm_eq_abs]`.
-/
theorem bounded_of_degree_zero {n : ℕ} (g : (Fin n → ℂ) → ℝ)
    (hdeg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x)
    (hc : ContinuousOn g {x | x ≠ 0}) : ∃ B : ℝ, ∀ x, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (hc.mono fun x hx => by
      rintro rfl
      simp at hx)
  refine ⟨max B |g 0|, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    exact le_max_right _ _
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hne : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0 := by simpa using hn
    rw [← hdeg _ x hne]
    refine le_trans ?_ (le_max_left _ _)
    have hmem : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ sphere (0 : Fin n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ hn]
    simpa [Real.norm_eq_abs] using hB _ hmem

/- English proof (translation)
Establish `h` using `ringKrullDim_quotient_le J`. Rewrite `h` using `[hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]`. Conclude with `h` after adjusting the coercions.
-/
theorem le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

/- English proof (translation)
Establish `hdet : IsUnit (h.matᵀ).det` using `by rw [det_transpose]; exact h.isUnit_det`. Set `P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)` to `LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 h.matᵀ)`. Set `Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)` to `LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (h.matᵀ)⁻¹)`. Establish `hsub : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} ⊆ Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1))`. Introduce and unpack `z ⟨hz, hzJ⟩`.

Use `⟨P z, ⟨fun q hq => hzJ q hq, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_ball_zero_iff]`. Combine the equalities or inequalities in the displayed calculation. Use extensionality with `i`. Simplify using `[P, Q, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]`.

Establish `hd : (0 : ℝ) ≤ ((2 * (e + 1) : ℕ) : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coneBall_hausdorff_lt_top (hMF : MassFinite.Statement) {n e : ℕ} (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} < ⊤ := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  let P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 h.matᵀ)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (h.matᵀ)⁻¹)
  have hsub : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} ⊆
      Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) := by
    rintro z ⟨hz, hzJ⟩
    refine ⟨P z, ⟨fun q hq => hzJ q hq, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
        _ ≤ ‖P‖ * 1 := by gcongr
        _ < ‖P‖ + 1 := by linarith
    · ext i
      simp [P, Q, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
  have hd : (0 : ℝ) ≤ ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  calc _ ≤ Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1))) :=
        measure_mono hsub
    _ ≤ (‖Q‖₊ : ENNReal) ^ ((2 * (e + 1) : ℕ) : ℝ) *
          Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) :=
        Q.lipschitz.hausdorffMeasure_image_le hd _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top)
        (hMF n (e + 1) J hJ (by exact_mod_cast hdim) _)

/- English proof (translation)
Establish `hdet : IsUnit (h.matᵀ).det` using `by rw [det_transpose]; exact h.isUnit_det`. Establish `hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Establish `hMx : (h.matᵀ)⁻¹ *ᵥ x ≠ 0`. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Rewrite using `[← hinv, h0, Matrix.mulVec_zero]`. Use `set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def`. Establish `hρx : h.dualNorm x = ρ`. Rewrite using `[hρ_def, EuclideanSpace.norm_eq]`.

Both sides reduce to the same expression. Establish `hρ : 0 < ρ`. Rewrite using `[hρ_def, norm_pos_iff]`. Introduce `h0`. Conclude with `hMx (by simpa using congrArg WithLp.ofLp h0)`.

Establish `hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x`. Introduce `t`. Establish `: (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x)`. Use extensionality with `i`. Simplify using the standard rewrite rules.

Simplify using `only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]`. Establish `hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z)) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume] fun t => (g x * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t`. Establish `h0 : ∀ᵐ t : ℂ, t ≠ 0`. Rewrite using `[ae_iff]`. Simplify using the standard rewrite rules.

Use `filter_upwards [h0] with t ht`. Establish `hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ`. Rewrite using `[norm_smul, lt_div_iff₀ hρ]`. Distinguish the cases in `hb : ‖t‖ < 1 / ρ`. Rewrite using `[indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)), indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t x ht]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))), indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_congr_ae hae, integral_const_mul, integral_indicator_ball_norm_pow e (by positivity), hρx]`. Rewrite using `[one_div, inv_pow, Nat.factorial_succ]`.

Establish `hρ' : ρ ^ (2 * (e + 1)) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_line_gram {n : ℕ} (e : ℕ) (h : HermNorm n) (g : (Fin n → ℂ) → ℝ)
    (hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z))
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (g x * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1)))) := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMx : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hinv, h0, Matrix.mulVec_zero]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρx : h.dualNorm x = ρ := by
    rw [hρ_def, EuclideanSpace.norm_eq]
    rfl
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    exact hMx (by simpa using congrArg WithLp.ofLp h0)
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => g (h.pointOf z)) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (g x * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hg t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  rw [integral_congr_ae hae, integral_const_mul,
    integral_indicator_ball_norm_pow e (by positivity), hρx]
  rw [one_div, inv_pow, Nat.factorial_succ]
  have hρ' : ρ ^ (2 * (e + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/- English proof (translation)
Introduce `n e h J ℓ g A hJ hdim hℓ hdeg hcont hA`. Use `set f : EuclideanSpace ℂ (Fin n) → ℝ := (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z)) with hf`. Establish `hset : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} = {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∩ ball 0 1`. Use extensionality with `z`. Simplify using `only [mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]`.

Conclude with `and_comm`. Establish `hgm : Measurable g` using `measurable_of_continuousOn_compl_singleton 0 (hcont.mono fun x hx => hx)`. Establish `hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z`. Unfold `HermNorm.pointOf`. Conclude with `continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)`.

Take `⟨B, hB⟩` from `bounded_of_degree_zero g hdeg hcont`. Establish `hfin` using `coneBall_hausdorff_lt_top hMF h J hJ.isPrime hdim`. Establish `hint : IntegrableOn f {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))`. Rewrite using `[IntegrableOn, hf, integrable_indicator_iff measurableSet_ball, IntegrableOn, Measure.restrict_restrict measurableSet_ball, inter_comm, ← hset]`. Establish `: IsFiniteMeasure ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0})` using `isFiniteMeasure_restrict.2 hfin.ne`.

Conclude with `Integrable.of_bound (hgm.comp hpm.measurable).aestronglyMeasurable B (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB _)`. Establish `key` using `hArea n e h J ℓ A f hJ hdim hℓ hA hint`. Establish `hterm : ∀ y : Fin e → ℂ, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ s => ∫ t : ℂ, f (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y)) * (‖t‖ ^ (2 * e) * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y)) y = Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * sheetSum (J ⊔ Ideal.span {linForm ℓ …`. Introduce `y`. Unfold `sheetSum`.

Rewrite using `[mul_finsum_mem]`. Use `finsum_mem_congr rfl fun x hx => ?_` and prove the remaining obligations. Use `split_ifs with hs`. Take `⟨-, -, -, -, hsx, -⟩` from `hs.choose_spec`. Establish `hy : hs.choose y = x` using `by rw [← hx.2]; exact hsx`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Establish `hmem` using `hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Simplify using `[linForm] at hmem`. Use `beta_reduce`.

Rewrite using `[hy]`. Conclude with `integral_line_gram e h g hdeg x hx0 _`. Simplify using the standard rewrite rules. Rewrite `key` using `[hterm, integral_const_mul]`. Take `⟨hM0, hMtop⟩` from `coordBall_mass (n := n) (m := e + 1) (le_of_ringKrullDim_quotient J hdim)`.

Establish `hM : 0 < (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0}).toReal` using `ENNReal.toReal_pos hM0.ne' hMtop.ne`. Establish `hc : (0 : ℝ) < Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)` using `by positivity`. Establish `hleft : ∫ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, f z ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) = ∫ z in {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0}, g (h.pointOf z) ∂(Measure.hausdorffMeasure ((2 * (e + …`. Rewrite using `[hf, setIntegral_indicator measurableSet_ball, hset]`. Rewrite `key` using `[hleft]`.

Unfold `coneIntegral`. Rewrite using `[div_eq_iff hM.ne']`. Rewrite `key` using `[mul_left_comm]`. Rewrite using `[mul_left_cancel₀ hc.ne' key, mul_comm]`.
-/
theorem ConeChartGram.proof (hArea : ConeSheetGram.Statement) (hMF : MassFinite.Statement) :
    ConeChartGram.Statement := by
  intro n e h J ℓ g A hJ hdim hℓ hdeg hcont hA
  set f : EuclideanSpace ℂ (Fin n) → ℝ :=
    (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z)) with hf
  have hset : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} =
      {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∩ ball 0 1 := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_ball_zero_iff]
    exact and_comm
  have hgm : Measurable g := measurable_of_continuousOn_compl_singleton 0 (hcont.mono fun x hx => hx)
  have hpm : Continuous fun z : EuclideanSpace ℂ (Fin n) => h.pointOf z := by
    unfold HermNorm.pointOf
    exact continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _)
  obtain ⟨B, hB⟩ := bounded_of_degree_zero g hdeg hcont
  have hfin := coneBall_hausdorff_lt_top hMF h J hJ.isPrime hdim
  have hint : IntegrableOn f {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [IntegrableOn, hf, integrable_indicator_iff measurableSet_ball, IntegrableOn,
      Measure.restrict_restrict measurableSet_ball, inter_comm, ← hset]
    have : IsFiniteMeasure ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict
        {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0}) :=
      isFiniteMeasure_restrict.2 hfin.ne
    exact Integrable.of_bound (hgm.comp hpm.measurable).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB _)
  have key := hArea n e h J ℓ A f hJ hdim hℓ hA hint
  have hterm : ∀ y : Fin e → ℂ, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
      (fun _ s => ∫ t : ℂ, f (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y)) *
        (‖t‖ ^ (2 * e) * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y)) y =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) * sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
        (fun x s => g x * ((e.factorial : ℝ) / Real.pi ^ e *
          gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y / h.dualNorm x ^ (2 * (e + 1)))) y := by
    intro y
    unfold sheetSum
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun x hx => ?_
    split_ifs with hs
    · obtain ⟨-, -, -, -, hsx, -⟩ := hs.choose_spec
      have hy : hs.choose y = x := by rw [← hx.2]; exact hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have hmem := hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        simp [linForm] at hmem
      beta_reduce
      rw [hy]
      exact integral_line_gram e h g hdeg x hx0 _
    · simp
  simp_rw [hterm, integral_const_mul] at key
  obtain ⟨hM0, hMtop⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_ringKrullDim_quotient J hdim)
  have hM : 0 < (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0}).toReal :=
    ENNReal.toReal_pos hM0.ne' hMtop.ne
  have hc : (0 : ℝ) < Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) := by positivity
  have hleft : ∫ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, f z
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫ z in {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0},
        g (h.pointOf z) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    rw [hf, setIntegral_indicator measurableSet_ball, hset]
  rw [hleft] at key
  unfold coneIntegral
  rw [div_eq_iff hM.ne']
  rw [mul_left_comm] at key
  rw [mul_left_cancel₀ hc.ne' key, mul_comm]

end

end GroundTheory.Heights₂.Heights
