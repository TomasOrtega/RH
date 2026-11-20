import Mathlib

open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat

namespace GlobalTheory.FlagVolume

/- English proof (translation)
Establish `hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) (r * ((A + r ^ 2) ^ (m + 2))⁻¹) r`. Introduce `r _`. Establish `hp : 0 < A + r ^ 2` using `by positivity`. Establish `h1 : HasDerivAt (fun r : ℝ ↦ A + r ^ 2) (2 * r) r`. Simplify using `using (hasDerivAt_pow 2 r).const_add A`.

Establish `h2` using `((h1.pow (m + 1)).const_mul (2 * ((m : ℝ) + 1))).fun_inv (show 2 * ((m : ℝ) + 1) * (A + r ^ 2) ^ (m + 1) ≠ 0 by positivity)`. Use `h2.fun_neg.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Pi.pow_apply, Nat.add_sub_cancel]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((A + r ^ 2) ^ (m + 2))⁻¹` using `fun r hr ↦ by`. Establish `: 0 < r` using `hr`. Check the signs of the components of the expression. Establish `hl : Tendsto (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) atTop (𝓝 0)`.

Rewrite using `[← neg_zero]`. Use `Tendsto.neg (Tendsto.inv_tendsto_atTop ?_)` and prove the remaining obligations. Use `Tendsto.const_mul_atTop (by positivity) ?_` and prove the remaining obligations. Conclude with `(tendsto_pow_atTop (Nat.succ_ne_zero m)).comp (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))`. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hnn hl) ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)), integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hl]`.

Simplify using the standard rewrite rules.
-/
theorem lintegral_radial {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal ((2 * (m + 1) * A ^ (m + 1))⁻¹) := by
  have hd : ∀ r ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹)
      (r * ((A + r ^ 2) ^ (m + 2))⁻¹) r := by
    intro r _
    have hp : 0 < A + r ^ 2 := by positivity
    have h1 : HasDerivAt (fun r : ℝ ↦ A + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add A
    have h2 := ((h1.pow (m + 1)).const_mul (2 * ((m : ℝ) + 1))).fun_inv
      (show 2 * ((m : ℝ) + 1) * (A + r ^ 2) ^ (m + 1) ≠ 0 by positivity)
    refine h2.fun_neg.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((A + r ^ 2) ^ (m + 2))⁻¹ := fun r hr ↦ by
    have : 0 < r := hr
    positivity
  have hl : Tendsto (fun r : ℝ ↦ -(2 * (m + 1) * (A + r ^ 2) ^ (m + 1))⁻¹) atTop (𝓝 0) := by
    rw [← neg_zero]
    refine Tendsto.neg (Tendsto.inv_tendsto_atTop ?_)
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp
      (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_deriv_of_nonneg' hd hnn hl)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hnn)),
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hnn hl]
  simp

/- English proof (translation)
Rewrite using `[← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]`. Establish `h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 • ENNReal.ofReal (((A + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹) = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal (p.1 * ((A + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ ↦ (1 : ℝ≥0∞)) p.2`. Use `setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_` and prove the remaining obligations. Simplify using `only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]`. Rewrite using `[ENNReal.ofReal_mul (le_of_lt hp.1)]`.

Rewrite using `[h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul (f := fun r : ℝ ↦ ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹)) (g := fun _ : ℝ ↦ (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop), lintegral_radial hA]`. Simplify using `only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_complex_inv_pow {A : ℝ} (hA : 0 < A) (m : ℕ) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) =
      ENNReal.ofReal (π / (m + 1) * (A ^ (m + 1))⁻¹) := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 •
      ENNReal.ofReal (((A + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ENNReal.ofReal (p.1 * ((A + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ ↦ (1 : ℝ≥0∞)) p.2 := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul (le_of_lt hp.1)]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ ↦ ENNReal.ofReal (r * ((A + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ ↦ (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop), lintegral_radial hA]
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/- English proof (translation)
Establish `h` using `(volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm`. Rewrite using `[← h.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod (fun a ↦ f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm a)) (hf.comp h.measurable).aemeasurable]`. Simplify using `[MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]`.
-/
theorem lintegral_fin_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ z : ℂ, ∫⁻ w : Fin n → ℂ, f (Fin.cons z w) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod
    (fun a ↦ f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0).symm a))
    (hf.comp h.measurable).aemeasurable]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `m A hA`. Establish `: (m ! : ℝ) ≠ 0` using `by positivity`. Simplify using `[volume_pi, this]`.

Consider the case `succ n ih`. Introduce `m A hA`. Rewrite using `[lintegral_fin_succ (by fun_prop)]`. Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]`. Establish `h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((A + ‖z‖ ^ 2 + ∑ k, ‖w k‖ ^ 2) ^ (m + n + 1 + 1))⁻¹) = ENNReal.ofReal (π ^ n * (m + 1)! / (m + 1 + n)!) * ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹)` using `fun z ↦ by`.

Rewrite using `[← ENNReal.ofReal_mul (by positivity), ← ih (m + 1) (by positivity), show m + 1 + n = m + n + 1 by ring]`. Simplify using `only [h]`. Rewrite using `[lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA, ← ENNReal.ofReal_mul (by positivity), show m + 1 + n = m + n + 1 by ring, Nat.factorial_succ m]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_pi_inv_pow (n : ℕ) : ∀ (m : ℕ) {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((A + ∑ k, ‖z k‖ ^ 2) ^ (m + n + 1))⁻¹) =
      ENNReal.ofReal (π ^ n * m ! / (m + n)! * (A ^ (m + 1))⁻¹) := by
  induction n with
  | zero =>
    intro m A hA
    have : (m ! : ℝ) ≠ 0 := by positivity
    simp [volume_pi, this]
  | succ n ih =>
    intro m A hA
    rw [lintegral_fin_succ (by fun_prop)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2 + ∑ k, ‖w k‖ ^ 2) ^ (m + n + 1 + 1))⁻¹) =
        ENNReal.ofReal (π ^ n * (m + 1)! / (m + 1 + n)!) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := fun z ↦ by
      rw [← ENNReal.ofReal_mul (by positivity), ← ih (m + 1) (by positivity),
        show m + 1 + n = m + n + 1 by ring]
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), show m + 1 + n = m + n + 1 by ring,
      Nat.factorial_succ m]
    congr 1
    push_cast
    field_simp
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A hA`. Simplify using `[volume_pi]`. Consider the case `succ n ih`.

Introduce `A hA`. Establish `hm : ∀ (N : ℕ) (B : ℝ), Measurable fun z : Fin N → ℂ ↦ ENNReal.ofReal (∏ i : Fin N, ((B + ∑ k, if k ≤ i then ‖z k‖ ^ 2 else 0) ^ 2)⁻¹)` using `fun N B ↦ by`. Use `ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦ ?_)` and prove the remaining obligations. Use `((Measurable.const_add (Finset.measurable_sum _ fun k _ ↦ ?_) B).pow_const 2).inv` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> fun_prop`.

Rewrite using `[lintegral_fin_succ (hm _ _)]`. Simplify using `only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc, Fin.zero_le, if_true, Fin.succ_le_succ_iff, Fin.le_zero_iff, Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero]`. Establish `h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ 2)⁻¹ * ∏ i : Fin n, ((A + ‖z‖ ^ 2 + ∑ k, if k ≤ i then ‖w k‖ ^ 2 else 0) ^ 2)⁻¹) = ENNReal.ofReal (π ^ n / n !) * ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (n + 2))⁻¹)` using `fun z ↦ by`. Simplify using `only [ENNReal.ofReal_mul (show 0 ≤ ((A + ‖z‖ ^ 2) ^ 2)⁻¹ by positivity)]`. Rewrite using `[lintegral_const_mul _ (hm _ _), ih (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h]`. Rewrite using `[lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA, ← ENNReal.ofReal_mul (by positivity), Nat.factorial_succ n]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_prod_partial_sums (n : ℕ) : ∀ {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
      (∏ i : Fin n, ((A + ∑ k, if k ≤ i then ‖z k‖ ^ 2 else 0) ^ 2)⁻¹) =
      ENNReal.ofReal (π ^ n / n ! * (A ^ n)⁻¹) := by
  induction n with
  | zero =>
    intro A hA
    simp [volume_pi]
  | succ n ih =>
    intro A hA
    have hm : ∀ (N : ℕ) (B : ℝ), Measurable fun z : Fin N → ℂ ↦ ENNReal.ofReal
        (∏ i : Fin N, ((B + ∑ k, if k ≤ i then ‖z k‖ ^ 2 else 0) ^ 2)⁻¹) := fun N B ↦ by
      refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦ ?_)
      refine ((Measurable.const_add (Finset.measurable_sum _ fun k _ ↦ ?_) B).pow_const 2).inv
      split_ifs <;> fun_prop
    rw [lintegral_fin_succ (hm _ _)]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc,
      Fin.zero_le, if_true, Fin.succ_le_succ_iff, Fin.le_zero_iff, Fin.succ_ne_zero, if_false,
      Finset.sum_const_zero, add_zero]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ 2)⁻¹ *
          ∏ i : Fin n, ((A + ‖z‖ ^ 2 + ∑ k, if k ≤ i then ‖w k‖ ^ 2 else 0) ^ 2)⁻¹) =
        ENNReal.ofReal (π ^ n / n !) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (n + 2))⁻¹) := fun z ↦ by
      simp only [ENNReal.ofReal_mul (show 0 ≤ ((A + ‖z‖ ^ 2) ^ 2)⁻¹ by positivity)]
      rw [lintegral_const_mul _ (hm _ _), ih (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), Nat.factorial_succ n]
    congr 1
    push_cast
    field_simp
    ring

/- English proof (translation)
Set `T : (n → ℂ) →ₗ[ℝ] (n → ℂ)` to `(Matrix.toLin' R.transpose).restrictScalars ℝ`. Establish `hT : LinearMap.det T = ‖R.det‖ ^ 2`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]`. Establish `hp : 0 < ‖R.det‖ ^ 2` using `by positivity`. Establish `hmap` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (n → ℂ)) (f := T) (hT ▸ hp.ne')`.

Establish `hTm : Measurable T` using `T.continuous_of_finiteDimensional.measurable`. Establish `h1 : ∫⁻ y, f (Matrix.vecMul y R) = ∫⁻ y, f (T y)`. Simplify using `[T, Matrix.mulVec_transpose]`. Rewrite using `[h1, ← lintegral_map hf hTm, hmap, lintegral_smul_measure, hT, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hp.le, abs_of_pos (inv_pos.2 hp), mul_inv_cancel₀ hp.ne']`. Simplify using the standard rewrite rules.
-/
theorem lintegral_comp_vecMul {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ)
    (hR : R.det ≠ 0) {f : (n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, f b = ENNReal.ofReal (‖R.det‖ ^ 2) * ∫⁻ y, f (Matrix.vecMul y R) := by
  let T : (n → ℂ) →ₗ[ℝ] (n → ℂ) := (Matrix.toLin' R.transpose).restrictScalars ℝ
  have hT : LinearMap.det T = ‖R.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (n → ℂ))
    (f := T) (hT ▸ hp.ne')
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have h1 : ∫⁻ y, f (Matrix.vecMul y R) = ∫⁻ y, f (T y) := by
    simp [T, Matrix.mulVec_transpose]
  rw [h1, ← lintegral_map hf hTm, hmap, lintegral_smul_measure, hT, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le, abs_of_pos (inv_pos.2 hp), mul_inv_cancel₀ hp.ne']
  simp

end GlobalTheory.FlagVolume
