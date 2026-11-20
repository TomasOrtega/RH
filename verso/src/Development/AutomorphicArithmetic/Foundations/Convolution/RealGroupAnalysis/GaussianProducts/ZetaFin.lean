import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Simplify using `[wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero, mul_assoc]`.
-/
private theorem adelicWeightFour_eq_product {F : Type} [Field F] [NumberField F] (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (x y z : A F) :
    wt4 L N ![0, x, y, z] = GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N x * (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N y * GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N z) := by
  simp [wt4, Fin.prod_univ_four, GlobalTheory.CompanionTheory.EpConvB.adeleWeight_zero, mul_assoc]

/- English proof (translation)
Rewrite using `[← (finTwoArrowEquiv F).symm.tsum_eq, ENNReal.tsum_prod' ]`. Simplify using `only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]`. Repeatedly rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]`.
-/
private theorem tsum_pi_fin_two_product {F : Type} (f : F → ℝ≥0∞) :
    ∑' ξ : Fin 2 → F, f (ξ 0) * f (ξ 1) = (∑' x, f x) * ∑' x, f x := by
  rw [← (finTwoArrowEquiv F).symm.tsum_eq, ENNReal.tsum_prod' ]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/- English proof (translation)
Establish `h1 : T * T ≤ (c * (1 + b)) * (c * (1 + b))` using `mul_le_mul hT hT hT0 (hT0.trans hT)`. Establish `h2 : (c * (1 + b)) * (c * (1 + b)) ≤ 2 * c ^ 2 * (1 + b ^ 2)`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg c) (sq_nonneg (1 - b))]`. Establish `h3 : b ^ 2 * w ≥ 0` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem real_bound {w b T c : ℝ} (hw : 0 ≤ w) (hb : 0 < b) (hT0 : 0 ≤ T) (hT : T ≤ c * (1 + b)) :
    b ^ 2 * (w * (T * T)) ≤ 2 * c ^ 2 * (w * b ^ 2 + w * b ^ 4) := by
  have h1 : T * T ≤ (c * (1 + b)) * (c * (1 + b)) := mul_le_mul hT hT hT0 (hT0.trans hT)
  have h2 : (c * (1 + b)) * (c * (1 + b)) ≤ 2 * c ^ 2 * (1 + b ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (1 - b))]
  have h3 : b ^ 2 * w ≥ 0 := by positivity
  calc b ^ 2 * (w * (T * T)) = (b ^ 2 * w) * (T * T) := by ring
    _ ≤ (b ^ 2 * w) * (2 * c ^ 2 * (1 + b ^ 2)) := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = _ := by ring

/- English proof (translation)
Introduce `F _ _`. Take `⟨A2, h2⟩` from `GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 2) (by norm_num)`. Take `⟨A4, h4⟩` from `GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 4) (by norm_num)`. Use `⟨max (max A2 A4) (Module.finrank ℚ F + 1), fun L => ?_⟩` and prove the remaining obligations. Use `set N := max (max A2 A4) (Module.finrank ℚ F + 1) with hN`.

Establish `hfr : Module.finrank ℚ F < N` using `lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.CompanionTheory.EpConvB.theta_bound L hfr`. Establish `I2` using `h2 L N ((le_max_left _ _).trans (le_max_left _ _))`. Establish `I4` using `h4 L N ((le_max_right _ _).trans (le_max_left _ _))`. Set `w : IdeleGroup F → ℝ` to `fun b => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (b : A F)`.

Set `G : IdeleGroup F → ℝ` to `fun b => 2 * c ^ 2 * (w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 2 + w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 4)`. Establish `hG : Integrable G (ideleMeasure F)`. Establish `e2 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) = fun t : IdeleGroup F => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (2 : ℝ)`. Use function extensionality and compare the values at `t`. Simplify using `only [w, UpperTheory.ConvolutionTheory.R2.ab]`.

Rewrite using `[← Real.rpow_natCast]`. Evaluate the numerical expressions. Establish `e4 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) = fun t : IdeleGroup F => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (4 : ℝ)`. Use function extensionality and compare the values at `t`. Simplify using `only [w, UpperTheory.ConvolutionTheory.R2.ab]`.

Rewrite using `[← Real.rpow_natCast]`. Evaluate the numerical expressions. Establish `J2 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) (ideleMeasure F)` using `e2 ▸ I2`. Establish `J4 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) (ideleMeasure F)` using `e4 ▸ I4`. Conclude with `(J2.add J4).const_mul (2 * c ^ 2)`.

Establish `key : ∀ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F, ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ≤ ENNReal.ofReal (G a⁻¹)`. Introduce `a`. Take `⟨hs, hb⟩` from `hc a`. Establish `hf0 : ∀ x : F, 0 ≤ GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x)` using `fun x => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _`. Use `set T : ℝ := ∑' x : F, GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) with hTdef`.

Establish `hT0 : 0 ≤ T` using `tsum_nonneg hf0`. Establish `hw0 : 0 ≤ w a⁻¹` using `GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _`. Establish `e : ∑' ξ : Fin 2 → F, ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) = ENNReal.ofReal (w a⁻¹ * (T * T))`. Establish `e1 : ∀ ξ : Fin 2 → F, ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) = ENNReal.ofReal (w a⁻¹) * ((fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 0) * (fun x : F => ENNRea …`. Introduce `ξ`.

Rewrite using `[adelicWeightFour_eq_product, ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (hf0 _)]`. Establish `t2` using `tsum_pi_fin_two_product (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x)))`. Use `beta_reduce at t2`. Repeatedly rewrite using `[e1]`. Rewrite using `[ENNReal.tsum_mul_left, t2, ← ENNReal.ofReal_tsum_of_nonneg hf0 hs, ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hT0]`.

Establish `hbpos : 0 < (UpperTheory.ConvolutionTheory.R2.ab a)⁻¹` using `inv_pos.mpr (M.ab_pos a)`. Establish `hr` using `real_bound hw0 hbpos hT0 hb`. Rewrite using `[e, M.wt, ← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Simplify `hr` using `only [G, M.ab_inv]`.

Use `haveI : (ideleMeasure F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _`. Establish `h3 : ∫⁻ a : IdeleGroup F, ENNReal.ofReal (G a⁻¹) ∂(ideleMeasure F) = ∫⁻ b : IdeleGroup F, ENNReal.ofReal (G b) ∂(ideleMeasure F)` using `lintegral_inv_eq_self (fun b => ENNReal.ofReal (G b))`. Conclude with `ne_top_of_le_ne_top (h3 ▸ hG.lintegral_lt_top.ne) (lintegral_mono key)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.zetaFin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ N : ℕ, ∀ L : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∫⁻ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
    ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ∂(ideleMeasure F) ≠ ⊤ := by
  intro F _ _
  obtain ⟨A2, h2⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 2) (by norm_num)
  obtain ⟨A4, h4⟩ := GlobalTheory.CompanionTheory.EpConvB.integrable_weight (K := F) (σ := 4) (by norm_num)
  refine ⟨max (max A2 A4) (Module.finrank ℚ F + 1), fun L => ?_⟩
  set N := max (max A2 A4) (Module.finrank ℚ F + 1) with hN
  have hfr : Module.finrank ℚ F < N := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CompanionTheory.EpConvB.theta_bound L hfr
  have I2 := h2 L N ((le_max_left _ _).trans (le_max_left _ _))
  have I4 := h4 L N ((le_max_right _ _).trans (le_max_left _ _))
  let w : IdeleGroup F → ℝ := fun b => GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (b : A F)
  let G : IdeleGroup F → ℝ := fun b => 2 * c ^ 2 * (w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 2 + w b * UpperTheory.ConvolutionTheory.R2.ab b ^ 4)
  have hG : Integrable G (ideleMeasure F) := by
    have e2 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (2 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have e4 : (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) = fun t : IdeleGroup F =>
        GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N (t : A F) * ((IdeleGroup.ideleModule F t : ℝ)) ^ (4 : ℝ) := by
      funext t
      simp only [w, UpperTheory.ConvolutionTheory.R2.ab]
      rw [← Real.rpow_natCast]
      norm_num
    have J2 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 2) (ideleMeasure F) := e2 ▸ I2
    have J4 : Integrable (fun t : IdeleGroup F => w t * UpperTheory.ConvolutionTheory.R2.ab t ^ 4) (ideleMeasure F) := e4 ▸ I4
    exact (J2.add J4).const_mul (2 * c ^ 2)
  have key : ∀ a : IdeleGroup F, M.wt a * ∑' ξ : Fin 2 → F,
      ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) ≤ ENNReal.ofReal (G a⁻¹) := by
    intro a
    obtain ⟨hs, hb⟩ := hc a
    have hf0 : ∀ x : F, 0 ≤ GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) :=
      fun x => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    set T : ℝ := ∑' x : F, GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x) with hTdef
    have hT0 : 0 ≤ T := tsum_nonneg hf0
    have hw0 : 0 ≤ w a⁻¹ := GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _
    have e : ∑' ξ : Fin 2 → F,
        ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
        ENNReal.ofReal (w a⁻¹ * (T * T)) := by
      have e1 : ∀ ξ : Fin 2 → F,
          ENNReal.ofReal (wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]) =
          ENNReal.ofReal (w a⁻¹) * ((fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 0) *
            (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x))) (ξ 1)) := by
        intro ξ
        rw [adelicWeightFour_eq_product, ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (hf0 _)]
      have t2 := tsum_pi_fin_two_product (fun x : F => ENNReal.ofReal (GlobalTheory.CompanionTheory.EpConvB.adeleWeight L N ((a : A F) * rt x)))
      beta_reduce at t2
      simp_rw [e1]
      rw [ENNReal.tsum_mul_left, t2, ← ENNReal.ofReal_tsum_of_nonneg hf0 hs,
        ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hT0]
    have hbpos : 0 < (UpperTheory.ConvolutionTheory.R2.ab a)⁻¹ := inv_pos.mpr (M.ab_pos a)
    have hr := real_bound hw0 hbpos hT0 hb
    rw [e, M.wt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa only [G, M.ab_inv] using hr
  haveI : (ideleMeasure F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _
  have h3 : ∫⁻ a : IdeleGroup F, ENNReal.ofReal (G a⁻¹) ∂(ideleMeasure F) = ∫⁻ b : IdeleGroup F, ENNReal.ofReal (G b) ∂(ideleMeasure F) :=
    lintegral_inv_eq_self (fun b => ENNReal.ofReal (G b))
  exact ne_top_of_le_ne_top (h3 ▸ hG.lintegral_lt_top.ne) (lintegral_mono key)
