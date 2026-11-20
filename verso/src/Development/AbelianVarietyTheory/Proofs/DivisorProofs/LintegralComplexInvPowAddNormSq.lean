import Mathlib

open Set Filter Topology MeasureTheory

namespace GlobalTheory.RadialIntegral

/- English proof (translation)
Establish `hp : 0 < a + r ^ 2` using `by positivity`. Establish `h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r`. Simplify using `using ((hasDerivAt_pow 2 r).const_add a)`. Establish `h2` using `((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)`. Use `h2.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [Pi.pow_apply, Nat.add_sub_cancel]`. Establish `: (m : ℝ) + 1 ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_prim (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by
  have hp : 0 < a + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add a)
  have h2 := ((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)
  refine h2.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop` using `tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)`. Establish `h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop` using `(tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1`. Simplify using `using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg`.
-/
lemma tendsto_prim (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1
  simpa using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg

/- English proof (translation)
Establish `hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹` using `fun r hr => by`. Establish `: (0 : ℝ) < r` using `hr`. Check the signs of the components of the expression. Establish `hint` using `integrableOn_Ioi_deriv_of_nonneg' (a := 0) (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)`. Establish `hval` using `integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)`.

Rewrite using `[← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]`. Simplify using the standard rewrite rules.
-/
lemma radial (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹ := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp

/- English proof (translation)
Rewrite using `[← Complex.lintegral_comp_polarCoord_symm]`. Establish `h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹) = ∫⁻ p in polarCoord.target, ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2`. Use `setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)` and prove the remaining obligations. Establish `h0 : 0 < p.1` using `hp.1`. Simplify using `only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]`.

Rewrite using `[ENNReal.ofReal_mul h0.le]`. Rewrite using `[h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)) (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]`. Simplify using `only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Ioo]`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_inv_pow_add_norm_sq (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹)
      = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have h0 : 0 < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul h0.le]
  rw [h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]
  simp only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end GlobalTheory.RadialIntegral
