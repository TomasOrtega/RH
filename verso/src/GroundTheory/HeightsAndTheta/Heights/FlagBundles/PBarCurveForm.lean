import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped ComplexConjugate Topology
open GroundTheory.Heights₂.Heights

noncomputable section

namespace BarCurve

/- English proof (translation)
Simplify using `[normSqSum]`.
-/
lemma normSqSum_one (u : Fin 1 → ℂ) : normSqSum u = ‖u 0‖ ^ 2 := by
  simp [normSqSum]

/- English proof (translation)
Unfold `normSqSum`. Use `fun_prop`.
-/
lemma continuous_normSqSum_one : Continuous (normSqSum : (Fin 1 → ℂ) → ℝ) := by
  unfold normSqSum; fun_prop

/- English proof (translation)
Establish `h` using `(((hasFDerivAt_normSqSum u).const_sub 1).log (sub_pos.mpr hu).ne').const_mul (1 / 2 : ℝ)`. Conclude with `Complex.ofRealCLM.hasFDerivAt.comp u h.neg`.
-/
lemma hasFDerivAt_pot (u : Fin 1 → ℂ) (hu : normSqSum u < 1) :
    HasFDerivAt (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (-((1 / 2 : ℝ) • ((1 - normSqSum u)⁻¹ • -dNormSqSum u)))) u := by
  have h := (((hasFDerivAt_normSqSum u).const_sub 1).log (sub_pos.mpr hu).ne').const_mul (1 / 2 : ℝ)
  exact Complex.ofRealCLM.hasFDerivAt.comp u h.neg

/- English proof (translation)
Rewrite using `[wirtingerBar, (hasFDerivAt_pot u hu).fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, neg_apply, FunLike.coe_smul, Pi.smul_apply, dNormSqSum_single, Complex.ofRealCLM_apply, smul_eq_mul]`. Establish `h1 : (1 * conj (u 0)).re = (u 0).re` using `by simp`. Establish `h2 : (Complex.I * conj (u 0)).re = (u 0).im` using `by simp`. Rewrite using `[h1, h2]`.

Use `conv_rhs => rw [← Complex.re_add_im (u 0)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma wirtingerBar_pot (u : Fin 1 → ℂ) (hu : normSqSum u < 1) :
    wirtingerBar (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)) 0 u =
      ((2⁻¹ * (1 - normSqSum u)⁻¹ : ℝ) : ℂ) * u 0 := by
  rw [wirtingerBar, (hasFDerivAt_pot u hu).fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, FunLike.coe_smul,
    Pi.smul_apply, dNormSqSum_single, Complex.ofRealCLM_apply, smul_eq_mul]
  have h1 : (1 * conj (u 0)).re = (u 0).re := by simp
  have h2 : (Complex.I * conj (u 0)).re = (u 0).im := by simp
  rw [h1, h2]
  conv_rhs => rw [← Complex.re_add_im (u 0)]
  push_cast
  ring

/- English proof (translation)
Use `filter_upwards [(isOpen_lt continuous_normSqSum_one continuous_const).mem_nhds hz] with w hw`. Rewrite using `[wirtingerBar_pot w hw, Complex.real_smul]`.
-/
lemma inner_eventuallyEq (z : Fin 1 → ℂ) (hz : normSqSum z < 1) :
    (fun w => wirtingerBar
        (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)) 0 w)
      =ᶠ[𝓝 z] fun w => (2⁻¹ * (1 - normSqSum w)⁻¹ : ℝ) • w 0 := by
  filter_upwards [(isOpen_lt continuous_normSqSum_one continuous_const).mem_nhds hz] with w hw
  rw [wirtingerBar_pot w hw, Complex.real_smul]

/- English proof (translation)
Establish `hinv : HasFDerivAt (fun w : Fin 1 → ℂ => (1 - normSqSum w)⁻¹) ((-((1 - normSqSum z) ^ 2)⁻¹) • -dNormSqSum z) z` using `(hasDerivAt_inv (sub_pos.mpr hz).ne').comp_hasFDerivAt z ((hasFDerivAt_normSqSum z).const_sub 1)`. Conclude with `(hinv.const_mul (2⁻¹ : ℝ)).smul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt`.
-/
lemma hasFDerivAt_inner (z : Fin 1 → ℂ) (hz : normSqSum z < 1) :
    HasFDerivAt (fun w : Fin 1 → ℂ => (2⁻¹ * (1 - normSqSum w)⁻¹ : ℝ) • w 0)
      ((2⁻¹ * (1 - normSqSum z)⁻¹) • (ContinuousLinearMap.proj 0 : (Fin 1 → ℂ) →L[ℝ] ℂ) +
        ((2⁻¹ : ℝ) • ((-((1 - normSqSum z) ^ 2)⁻¹) • -dNormSqSum z)).smulRight (z 0)) z := by
  have hinv : HasFDerivAt (fun w : Fin 1 → ℂ => (1 - normSqSum w)⁻¹)
      ((-((1 - normSqSum z) ^ 2)⁻¹) • -dNormSqSum z) z :=
    (hasDerivAt_inv (sub_pos.mpr hz).ne').comp_hasFDerivAt z
      ((hasFDerivAt_normSqSum z).const_sub 1)
  exact (hinv.const_mul (2⁻¹ : ℝ)).smul
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt

/- English proof (translation)
Rewrite using `[wirtinger, (inner_eventuallyEq z hz).fderiv_eq, (hasFDerivAt_inner z hz).fderiv]`. Simplify using `only [add_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.smulRight_apply, neg_apply, dNormSqSum_single, Pi.single_eq_same, smul_eq_mul, Complex.real_smul]`. Establish `h1 : (1 * conj (z 0)).re = (z 0).re` using `by simp`. Establish `h2 : (Complex.I * conj (z 0)).re = (z 0).im` using `by simp`. Rewrite using `[h1, h2]`.

Establish `hS : normSqSum z = (z 0).re ^ 2 + (z 0).im ^ 2`. Rewrite using `[normSqSum_one, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : (1 - normSqSum z) ≠ 0` using `(sub_pos.mpr hz).ne'`. Establish `hc : ((1 - normSqSum z : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast ht`.

Use `conv_lhs => rw [← Complex.re_add_im (z 0)]`. Establish `hSc : ((normSqSum z : ℝ) : ℂ) = ((z 0).re : ℂ) ^ 2 + ((z 0).im : ℂ) ^ 2`. Rewrite using `[hS]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Move the coercions through the operations in `at hc ⊢`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hSc]`. Simplify using `only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]`. Use `push_cast`.

Take the linear combination `(((z 0).re : ℂ) ^ 2 - ((z 0).im : ℂ) ^ 2 - 1) * Complex.I_sq`.
-/
lemma wirtinger_wirtingerBar_pot (z : Fin 1 → ℂ) (hz : normSqSum z < 1) :
    wirtinger (fun w => wirtingerBar
        (fun v : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)) 0 w) 0 z =
      ((2⁻¹ * ((1 - normSqSum z) ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [wirtinger, (inner_eventuallyEq z hz).fderiv_eq, (hasFDerivAt_inner z hz).fderiv]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.smulRight_apply,
    neg_apply, dNormSqSum_single, Pi.single_eq_same, smul_eq_mul,
    Complex.real_smul]
  have h1 : (1 * conj (z 0)).re = (z 0).re := by simp
  have h2 : (Complex.I * conj (z 0)).re = (z 0).im := by simp
  rw [h1, h2]
  have hS : normSqSum z = (z 0).re ^ 2 + (z 0).im ^ 2 := by
    rw [normSqSum_one, Complex.sq_norm, Complex.normSq_apply]; ring
  have ht : (1 - normSqSum z) ≠ 0 := (sub_pos.mpr hz).ne'
  have hc : ((1 - normSqSum z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  conv_lhs => rw [← Complex.re_add_im (z 0)]
  have hSc : ((normSqSum z : ℝ) : ℂ) = ((z 0).re : ℂ) ^ 2 + ((z 0).im : ℂ) ^ 2 := by
    rw [hS]; push_cast; ring
  push_cast at hc ⊢
  field_simp
  rw [hSc]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  linear_combination (((z 0).re : ℂ) ^ 2 - ((z 0).im : ℂ) ^ 2 - 1) * Complex.I_sq

end BarCurve

/- English proof (translation)
Introduce `z hz`. Establish `hz' : normSqSum (fun _ : Fin 1 => z) < 1`. Rewrite using `[BarCurve.normSqSum_one]`. Use `norm_nonneg z` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hfun : (fun u : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - ‖u 0‖ ^ 2)) : ℝ) : ℂ)) = fun v => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`. Rewrite using `[BarCurve.normSqSum_one]`. Establish `hkey : ddcDensity (fun w => -((1 / 2) * Real.log (1 - ‖w‖ ^ 2))) z = Real.pi⁻¹ / (1 - ‖z‖ ^ 2) ^ 2`. Simplify using `only [ddcDensity]`.

Rewrite using `[hfun, BarCurve.wirtinger_wirtingerBar_pot _ hz', Complex.ofReal_re, BarCurve.normSqSum_one]`. Establish `hpi` using `Real.pi_ne_zero`. Establish `ht : (1 - ‖z‖ ^ 2) ≠ 0`. Use `norm_nonneg z` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Clear the denominators using the available nonvanishing facts. Use `⟨hkey, ?_⟩` and prove the remaining obligations. Rewrite using `[hkey]`. Establish `ht : 0 < 1 - ‖z‖ ^ 2`. Use `norm_nonneg z` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Check the signs of the components of the expression.
-/
theorem BarCurveForm.proof : BarCurveForm.Statement := by
  intro z hz
  have hz' : normSqSum (fun _ : Fin 1 => z) < 1 := by
    rw [BarCurve.normSqSum_one]
    have := norm_nonneg z
    nlinarith
  have hfun : (fun u : Fin 1 → ℂ => ((-(1 / 2 * Real.log (1 - ‖u 0‖ ^ 2)) : ℝ) : ℂ)) =
      fun v => ((-(1 / 2 * Real.log (1 - normSqSum v)) : ℝ) : ℂ) := by
    funext v; rw [BarCurve.normSqSum_one]
  have hkey : ddcDensity (fun w => -((1 / 2) * Real.log (1 - ‖w‖ ^ 2))) z =
      Real.pi⁻¹ / (1 - ‖z‖ ^ 2) ^ 2 := by
    simp only [ddcDensity]
    rw [hfun, BarCurve.wirtinger_wirtingerBar_pot _ hz', Complex.ofReal_re,
      BarCurve.normSqSum_one]
    have hpi := Real.pi_ne_zero
    have ht : (1 - ‖z‖ ^ 2) ≠ 0 := by
      have := norm_nonneg z
      nlinarith
    field_simp
  refine ⟨hkey, ?_⟩
  rw [hkey]
  have ht : 0 < 1 - ‖z‖ ^ 2 := by
    have := norm_nonneg z
    nlinarith
  positivity

end

end GroundTheory.Heights₂.Heights.FlagBundles
