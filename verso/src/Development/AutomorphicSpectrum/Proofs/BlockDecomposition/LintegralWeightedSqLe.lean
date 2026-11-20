import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.Schur

/- English proof (translation)
Establish `hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a` using `fun a => by`. Rewrite using `[← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]`. Evaluate the numerical expressions. Establish `hs : Measurable fun y => u y ^ (1 / 2 : ℝ)` using `hu.pow_const _`. Establish `h` using `ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hs.aemeasurable (hs.mul hg).aemeasurable`.

Establish `e1 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * ((fun y => u y ^ (1 / 2 : ℝ)) * g)) a ∂ν = ∫⁻ y, u y * g y ∂ν`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Rewrite using `[← mul_assoc, ← sq, hsq]`. Establish `e2 : ∫⁻ a, (u a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂ν = ∫⁻ y, u y ∂ν`.

Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.rpow_two, hsq]`. Establish `e3 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * g) a ^ (2 : ℝ) ∂ν = ∫⁻ y, u y * g y ^ 2 ∂ν`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`.

Rewrite using `[ENNReal.rpow_two, mul_pow, hsq]`. Rewrite `h` using `[e1, e2, e3]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_weighted_sq_le {α : Type} [MeasurableSpace α] (ν : Measure α)
    (u g : α → ℝ≥0∞) (hu : Measurable u) (hg : Measurable g) :
    (∫⁻ y, u y * g y ∂ν) ^ 2 ≤ (∫⁻ y, u y ∂ν) * ∫⁻ y, u y * g y ^ 2 ∂ν := by
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hs : Measurable fun y => u y ^ (1 / 2 : ℝ) := hu.pow_const _
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hs.aemeasurable
    (hs.mul hg).aemeasurable
  have e1 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * ((fun y => u y ^ (1 / 2 : ℝ)) * g)) a ∂ν
      = ∫⁻ y, u y * g y ∂ν := by
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← sq, hsq]
  have e2 : ∫⁻ a, (u a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂ν = ∫⁻ y, u y ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.rpow_two, hsq]
  have e3 : ∫⁻ a, ((fun y => u y ^ (1 / 2 : ℝ)) * g) a ^ (2 : ℝ) ∂ν = ∫⁻ y, u y * g y ^ 2 ∂ν := by
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.rpow_two, mul_pow, hsq]
  rw [e1, e2, e3] at h
  calc (∫⁻ y, u y * g y ∂ν) ^ 2 ≤ _ := pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, hsq, hsq]

/- English proof (translation)
Introduce `α _ ν _ k A f hk hf hrow hcol`. Establish `hk1 : ∀ x, Measurable (k x)` using `fun x => hk.of_uncurry_left`. Establish `hk2 : ∀ y, Measurable fun x => k x y` using `fun y => hk.of_uncurry_right`. Establish `hgm : Measurable (hf.mk f)` using `hf.measurable_mk`. Use `set g := hf.mk f with hgdef`.

Establish `hfg : f =ᵐ[ν] g` using `hf.ae_eq_mk`. Establish `e1 : ∀ x, ∫⁻ y, k x y * f y ∂ν = ∫⁻ y, k x y * g y ∂ν` using `fun x => lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])`. Establish `e2 : ∫⁻ y, f y ^ 2 ∂ν = ∫⁻ y, g y ^ 2 ∂ν` using `lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])`. Establish `hF : Measurable (Function.uncurry fun x y => k x y * g y ^ 2)` using `hk.mul ((hgm.pow_const 2).comp measurable_snd)`. Establish `hQ : Measurable fun x => ∫⁻ y, k x y * g y ^ 2 ∂ν` using `hF.lintegral_prod_right'`.

Simplify using `only [e1, e2]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Conclude with `(lintegral_weighted_sq_le ν (k x) g (hk1 x) hgm).trans (by gcongr; exact hrow x)`. Use `_ = A * ∫⁻ x, ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := lintegral_const_mul _ hQ`.

Use `_ = A * ∫⁻ y, ∫⁻ x, k x y * g y ^ 2 ∂ν ∂ν := by`. Rewrite using `[lintegral_lintegral_swap hF.aemeasurable]`. Use `_ = A * ∫⁻ y, (∫⁻ x, k x y ∂ν) * g y ^ 2 ∂ν := by`. Use `congr 1`. Conclude with `lintegral_congr fun y => lintegral_mul_const _ (hk2 y)`.

Use `_ ≤ A * ∫⁻ y, A * g y ^ 2 ∂ν := by gcongr with y`. Conclude with `hcol y`. Use `_ = A ^ 2 * ∫⁻ y, g y ^ 2 ∂ν := by`. Rewrite using `[lintegral_const_mul _ (hgm.pow_const 2), sq, mul_assoc]`.
-/
theorem schurL : SchurL := by
  intro α _ ν _ k A f hk hf hrow hcol
  have hk1 : ∀ x, Measurable (k x) := fun x => hk.of_uncurry_left
  have hk2 : ∀ y, Measurable fun x => k x y := fun y => hk.of_uncurry_right
  have hgm : Measurable (hf.mk f) := hf.measurable_mk
  set g := hf.mk f with hgdef
  have hfg : f =ᵐ[ν] g := hf.ae_eq_mk
  have e1 : ∀ x, ∫⁻ y, k x y * f y ∂ν = ∫⁻ y, k x y * g y ∂ν := fun x =>
    lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have e2 : ∫⁻ y, f y ^ 2 ∂ν = ∫⁻ y, g y ^ 2 ∂ν :=
    lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have hF : Measurable (Function.uncurry fun x y => k x y * g y ^ 2) :=
    hk.mul ((hgm.pow_const 2).comp measurable_snd)
  have hQ : Measurable fun x => ∫⁻ y, k x y * g y ^ 2 ∂ν := hF.lintegral_prod_right'
  simp only [e1, e2]
  calc ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, A * ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := by
        refine lintegral_mono fun x => ?_
        exact (lintegral_weighted_sq_le ν (k x) g (hk1 x) hgm).trans (by gcongr; exact hrow x)
    _ = A * ∫⁻ x, ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := lintegral_const_mul _ hQ
    _ = A * ∫⁻ y, ∫⁻ x, k x y * g y ^ 2 ∂ν ∂ν := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ = A * ∫⁻ y, (∫⁻ x, k x y ∂ν) * g y ^ 2 ∂ν := by
        congr 1
        exact lintegral_congr fun y => lintegral_mul_const _ (hk2 y)
    _ ≤ A * ∫⁻ y, A * g y ^ 2 ∂ν := by
        gcongr with y
        exact hcol y
    _ = A ^ 2 * ∫⁻ y, g y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hgm.pow_const 2), sq, mul_assoc]

end GlobalTheory.CompanionTheory.Schur
