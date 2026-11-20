import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ConvSeries.WeightedPowerFormIntegrability

open GlobalTheory.ConvSeries

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- English proof (translation)
Rewrite using `[← Complex.ofReal_neg, Complex.norm_exp_ofReal]`.
-/
lemma norm_cexp_neg_ofReal (x : ℝ) : ‖Complex.exp (-((x : ℝ) : ℂ))‖ = Real.exp (-x) := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

/- English proof (translation)
Unfold `wt`. Rewrite using `[norm_mul, norm_mul, norm_cexp_neg_ofReal, norm_cexp_neg_ofReal]`. Establish `h1` using `SchwartzMap.norm_le_seminorm ℝ h a`. Establish `hs : Real.exp (-((b + c) * ‖a‖ ^ 2)) = Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))`. Rewrite using `[← Real.exp_add]`.

Put the polynomial expressions in normal form. Rewrite using `[hs]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_wt_le (b c : ℝ) (h : SchwartzMap E ℂ) (a : E) :
    ‖wt b c h a‖ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2)) := by
  unfold wt
  rw [norm_mul, norm_mul, norm_cexp_neg_ofReal, norm_cexp_neg_ofReal]
  have h1 := SchwartzMap.norm_le_seminorm ℝ h a
  have hs : Real.exp (-((b + c) * ‖a‖ ^ 2)) =
      Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hs]
  calc Real.exp (-(b * ‖a‖ ^ 2)) * ‖h a‖ * Real.exp (-(c * ‖a‖ ^ 2))
      = ‖h a‖ * (Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))) := by ring
    _ ≤ SchwartzMap.seminorm ℝ 0 0 h * (Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

/- English proof (translation)
Establish `hc : Continuous (h : E → ℂ)` using `h.continuous`. Unfold `wt`. Use `fun_prop`.
-/
lemma continuous_wt (b c : ℝ) (h : SchwartzMap E ℂ) : Continuous (wt b c h) := by
  have hc : Continuous (h : E → ℂ) := h.continuous
  unfold wt
  fun_prop

/- English proof (translation)
Unfold `innerC`. Use `(ContinuousLinearMap.opNorm_comp_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Complex.ofRealCLM_norm, one_mul, innerSL_apply_norm]`.
-/
lemma norm_innerC_le (a : E) : ‖innerC a‖ ≤ ‖a‖ := by
  unfold innerC
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [Complex.ofRealCLM_norm, one_mul, innerSL_apply_norm]

/- English proof (translation)
Unfold `powForm`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `gcongr`. Conclude with `norm_innerC_le a`.
-/
lemma norm_powForm_le (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ * ‖a‖ ^ k := by
  unfold powForm
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact norm_innerC_le a

/- English proof (translation)
Establish `hi : Continuous (fun a : E => innerC a)`. Unfold `innerC`. Conclude with `continuous_const.clm_comp (innerSL ℝ (E := E)).continuous`. Establish `hf : (fun a : E => powForm k a) = fun a => (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin k => E) (fun _ => ℂ) ℂ (fun _ => innerC a)) (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ)`. Use function extensionality and compare the values at `a`.

Both sides reduce to the same expression. Rewrite using `[hf]`. Conclude with `((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin k => E) (fun _ => ℂ) ℂ).cont.comp (continuous_pi fun _ => hi)).clm_apply continuous_const`.
-/
lemma continuous_powForm (k : ℕ) : Continuous (fun a : E => powForm k a) := by
  have hi : Continuous (fun a : E => innerC a) := by
    unfold innerC
    exact continuous_const.clm_comp (innerSL ℝ (E := E)).continuous
  have hf : (fun a : E => powForm k a) = fun a =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ => ℂ) ℂ (fun _ => innerC a))
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ) := by
    funext a; rfl
  rw [hf]
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ => ℂ) ℂ).cont.comp (continuous_pi fun _ => hi)).clm_apply
    continuous_const

/- English proof (translation)
Establish `h1 : x ^ k ≤ k.factorial * Real.exp x`. Use `Real.pow_div_factorial_le_exp x hx k` as an intermediate fact. Rewrite `this` using `[div_le_iff₀ (by positivity), mul_comm]`. Then use the resulting hypothesis. Establish `h2 : x - β * x ^ 2 ≤ 1 / (2 * β) - β / 2 * x ^ 2`. Establish `ht : 1 / (2 * β) * (2 * β) = 1` using `by field_simp`.

Use polynomial arithmetic with `[sq_nonneg (β * x - 1)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Real.exp_add]`. Put the polynomial expressions in normal form. Use `_ ≤ k.factorial * Real.exp (1 / (2 * β) - β / 2 * x ^ 2) := by gcongr`.

Use `_ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf`.
-/
lemma pow_mul_exp_le {β : ℝ} (hβ : 0 < β) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(β * x ^ 2)) ≤
      k.factorial * Real.exp (1 / (2 * β)) * Real.exp (-(β / 2 * x ^ 2)) := by
  have h1 : x ^ k ≤ k.factorial * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx k
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : x - β * x ^ 2 ≤ 1 / (2 * β) - β / 2 * x ^ 2 := by
    have ht : 1 / (2 * β) * (2 * β) = 1 := by field_simp
    nlinarith [sq_nonneg (β * x - 1)]
  calc x ^ k * Real.exp (-(β * x ^ 2)) ≤ (k.factorial * Real.exp x) * Real.exp (-(β * x ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = k.factorial * Real.exp (x - β * x ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ k.factorial * Real.exp (1 / (2 * β) - β / 2 * x ^ 2) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Use `(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (β : ℂ)) (by simpa using hβ) 0 (0 : E)).norm` as an intermediate fact. Use `this.congr (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [zero_mul, add_zero]`. Rewrite using `[show -(β : ℂ) * (‖a‖ : ℂ) ^ 2 = ((-(β * ‖a‖ ^ 2) : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]`.
-/
lemma integrable_gauss {β : ℝ} (hβ : 0 < β) :
    Integrable (fun a : E => Real.exp (-(β * ‖a‖ ^ 2))) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (β : ℂ))
    (by simpa using hβ) 0 (0 : E)).norm
  refine this.congr (Eventually.of_forall fun a => ?_)
  simp only [zero_mul, add_zero]
  rw [show -(β : ℂ) * (‖a‖ : ℂ) ^ 2 = ((-(β * ‖a‖ ^ 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_ofReal]

/- English proof (translation)
Establish `hβ : 0 < b + c` using `by positivity`. Establish `hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h` using `apply_nonneg _ _`. Use `Integrable.mono' ((integrable_gauss (E := E) (half_pos hβ)).const_mul (SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ * k.factorial * Real.exp (1 / (2 * (b + c))))) ((continuous_wt b c h).smul (continuous_powForm k)).aestronglyMeasurable (Eventu …` and prove the remaining obligations. Rewrite using `[norm_smul]`. Establish `h1` using `norm_wt_le b c h a`.

Establish `h2` using `norm_powForm_le k a`. Establish `h3` using `pow_mul_exp_le hβ k (norm_nonneg a)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma integrable_wt_smul_powForm {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : SchwartzMap E ℂ)
    (k : ℕ) : Integrable (fun a : E => wt b c h a • powForm k a) := by
  have hβ : 0 < b + c := by positivity
  have hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h := apply_nonneg _ _
  refine Integrable.mono' ((integrable_gauss (E := E) (half_pos hβ)).const_mul
    (SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ *
      k.factorial * Real.exp (1 / (2 * (b + c)))))
    ((continuous_wt b c h).smul (continuous_powForm k)).aestronglyMeasurable
    (Eventually.of_forall fun a => ?_)
  rw [norm_smul]
  have h1 := norm_wt_le b c h a
  have h2 := norm_powForm_le k a
  have h3 := pow_mul_exp_le hβ k (norm_nonneg a)
  calc ‖wt b c h a‖ * ‖powForm k a‖
      ≤ (SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2))) *
          (‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ * ‖a‖ ^ k) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ *
          (‖a‖ ^ k * Real.exp (-((b + c) * ‖a‖ ^ 2))) := by ring
    _ ≤ SchwartzMap.seminorm ℝ 0 0 h * ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ‖ *
          (k.factorial * Real.exp (1 / (2 * (b + c))) * Real.exp (-((b + c) / 2 * ‖a‖ ^ 2))) := by
        gcongr
    _ = _ := by ring

/- English proof (translation)
Use `ContinuousLinearMap.integral_comp_comm (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ (fun _ => y)) (integrable_wt_smul_powForm hb hc h k)` as an intermediate fact. Simplify using `only [ContinuousMultilinearMap.apply_apply] at this`. Unfold `coef`. Rewrite using `[← this]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Simplify using `[powForm, innerC, ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_const]`.
-/
lemma coef_apply_const {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (h : SchwartzMap E ℂ) (k : ℕ) (y : E) :
    coef b c h k (fun _ => y) = ∫ a, wt b c h a * ((inner ℝ a y : ℝ) : ℂ) ^ k := by
  have := ContinuousLinearMap.integral_comp_comm
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ (fun _ => y))
    (integrable_wt_smul_powForm hb hc h k)
  simp only [ContinuousMultilinearMap.apply_apply] at this
  unfold coef
  rw [← this]
  congr 1; funext a
  simp [powForm, innerC, ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_const]

end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability

namespace GlobalTheory.ConvSeries

open GlobalTheory.ConvSeries.WeightedPowerFormIntegrability

/- English proof (translation)
Use `set z : E → ℂ := fun a => ((2 * c * inner ℝ a y : ℝ) : ℂ) with hz`. Establish `hzc : Continuous z` using `by rw [hz]; fun_prop`. Set `F : ℕ → E → ℂ` to `fun n a => wt b c h a * (z a ^ n / (n.factorial : ℂ))`. Establish `hF : ∀ n, (∫ a, F n a) = (((2 * c) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * coef b c h n (fun _ => y)`. Introduce `n`.

Rewrite using `[coef_apply_const hb hc h n y, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [F, z]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : HasSum (fun n => ∫ a, F n a) (∫ a, wt b c h a * Complex.exp (z a))`. Use `hasSum_integral_of_dominated_convergence (fun n a => ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `n`. Use `continuous_wt b c h` as an intermediate fact.

Conclude with `(by simp only [F]; fun_prop : Continuous (F n)).aestronglyMeasurable`. Introduce `n`. Use `Eventually.of_forall fun a => ?_` and prove the remaining obligations. Simplify using `only [F]`. Rewrite using `[norm_mul, norm_div, norm_pow, Complex.norm_natCast]`.

Establish `hza : ‖z a‖ ≤ 2 * c * ‖a‖ * ‖y‖`. Establish `h1 : ‖z a‖ = 2 * c * |inner ℝ a y|`. Simplify using `only [z, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two, abs_of_pos hc]`. Rewrite using `[h1]`. Use `abs_real_inner_le_norm a y` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use `gcongr`. Conclude with `Eventually.of_forall fun a => (Real.summable_pow_div_factorial _).mul_left _`. Establish `hts : (fun a => ∑' n : ℕ, ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) = fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)`. Use function extensionality and compare the values at `a`.

Rewrite using `[tsum_mul_left, Real.exp_eq_exp_ℝ, ← (NormedSpace.expSeries_div_hasSum_exp (2 * c * ‖a‖ * ‖y‖)).tsum_eq]`. Rewrite using `[hts]`. Establish `hcw` using `continuous_wt b c h`. Use `Integrable.mono' ((integrable_gauss (E := E) hb).const_mul (SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2))) (by fun_prop : Continuous fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)).aestronglyMeasurable (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.

Establish `hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h` using `apply_nonneg _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2 + -(b * ‖a‖ ^ 2)) := by`.

Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC` and prove the remaining obligations. Use polynomial arithmetic with `[sq_nonneg (‖a‖ - ‖y‖)]`. Use `_ = _ := by rw [Real.exp_add]; ring`. Use `Eventually.of_forall fun a => ?_` and prove the remaining obligations. Rewrite using `[Complex.exp_eq_exp_ℂ]`.

Conclude with `(NormedSpace.expSeries_div_hasSum_exp (z a)).mul_left (wt b c h a)`. Establish `e1 : (fun k => term b c h k y) = fun i => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, F i a`. Use function extensionality and compare the values at `k`. Simplify using `only [term]`. Rewrite using `[hF]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, wt b c h a * Complex.exp (z a)`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Establish `key : Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (z a) = Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [z]`. Rewrite using `[norm_sub_sq_real, real_inner_comm a y]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `wt`. Take the linear combination `(-(Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a)) * key`. Rewrite using `[e1, e2]`.

Conclude with `hsum.mul_left _`.
-/
theorem hasSum_term_integral (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (h : SchwartzMap E ℂ) (y : E) :
    HasSum (fun k => term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  set z : E → ℂ := fun a => ((2 * c * inner ℝ a y : ℝ) : ℂ) with hz
  have hzc : Continuous z := by rw [hz]; fun_prop
  let F : ℕ → E → ℂ := fun n a => wt b c h a * (z a ^ n / (n.factorial : ℂ))
  have hF : ∀ n, (∫ a, F n a) =
      (((2 * c) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * coef b c h n (fun _ => y) := by
    intro n
    rw [coef_apply_const hb hc h n y, ← integral_const_mul]
    congr 1; funext a
    simp only [F, z]; push_cast; ring
  have hsum : HasSum (fun n => ∫ a, F n a) (∫ a, wt b c h a * Complex.exp (z a)) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n a => ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) ?_ ?_ ?_ ?_ ?_
    · intro n
      have := continuous_wt b c h
      exact (by simp only [F]; fun_prop : Continuous (F n)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun a => ?_
      simp only [F]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have hza : ‖z a‖ ≤ 2 * c * ‖a‖ * ‖y‖ := by
        have h1 : ‖z a‖ = 2 * c * |inner ℝ a y| := by
          simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two, abs_of_pos hc]
        rw [h1]
        have := abs_real_inner_le_norm a y
        nlinarith
      gcongr
    · exact Eventually.of_forall fun a => (Real.summable_pow_div_factorial _).mul_left _
    · have hts : (fun a => ∑' n : ℕ, ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) =
          fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖) := by
        funext a
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ,
          ← (NormedSpace.expSeries_div_hasSum_exp (2 * c * ‖a‖ * ‖y‖)).tsum_eq]
      rw [hts]
      have hcw := continuous_wt b c h
      refine Integrable.mono' ((integrable_gauss (E := E) hb).const_mul
        (SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2)))
        (by fun_prop : Continuous fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)).aestronglyMeasurable
        (Eventually.of_forall fun a => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h := apply_nonneg _ _
      calc ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)
          ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2)) *
              Real.exp (2 * c * ‖a‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_right (norm_wt_le b c h a) (by positivity)
        _ = SchwartzMap.seminorm ℝ 0 0 h *
              Real.exp (-((b + c) * ‖a‖ ^ 2) + 2 * c * ‖a‖ * ‖y‖) := by
            rw [Real.exp_add]; ring
        _ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2 + -(b * ‖a‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
            nlinarith [sq_nonneg (‖a‖ - ‖y‖)]
        _ = _ := by rw [Real.exp_add]; ring
    · refine Eventually.of_forall fun a => ?_
      rw [Complex.exp_eq_exp_ℂ]
      exact (NormedSpace.expSeries_div_hasSum_exp (z a)).mul_left (wt b c h a)
  have e1 : (fun k => term b c h k y) =
      fun i => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, F i a := by
    funext k
    simp only [term]
    rw [hF]; ring
  have e2 : (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) =
      Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, wt b c h a * Complex.exp (z a) := by
    rw [← integral_const_mul]
    congr 1; funext a
    have key : Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ)) *
        Complex.exp (z a) = Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [z]
      rw [norm_sub_sq_real, real_inner_comm a y]
      push_cast; ring
    unfold wt
    linear_combination (-(Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a)) * key
  rw [e1, e2]
  exact hsum.mul_left _

end GlobalTheory.ConvSeries
