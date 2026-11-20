import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Use `haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by infer_instance`. Use `haveI hS : SigmaFinite (volume : Measure ℂ) := by infer_instance`. Use `haveI h1 : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := by`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi.isAddHaarMeasure _`.

Use `haveI hS1 : SigmaFinite (volume : Measure (Fin N → ℂ)) := by infer_instance`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem matrix_space_volume_isAddHaar (N : ℕ) : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := by
  haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by infer_instance
  haveI hS : SigmaFinite (volume : Measure ℂ) := by infer_instance
  haveI h1 : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  haveI hS1 : SigmaFinite (volume : Measure (Fin N → ℂ)) := by infer_instance
  rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _

def leftMulLinearMap (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (g * Matrix.of Z)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

def rightMulLinear (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (Matrix.of Z * g)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]; ring_nf

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `Z`. Use function extensionality and compare the values at `i j`. Simplify using `[rightMulLinear, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem right_mul_map_eq_pi_toLin (g : Matrix (Fin N) (Fin N) ℂ) :
    rightMulLinear g = LinearMap.pi (fun i : Fin N => (Matrix.toLin' gᵀ).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro Z; funext i j
  simp [rightMulLinear, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

/- English proof (translation)
Rewrite using `[right_mul_map_eq_pi_toLin, LinearMap.det_pi]`. Simplify using `[LinearMap.det_toLin', Matrix.det_transpose]`.
-/
theorem det_right_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (rightMulLinear g) = g.det ^ N := by
  rw [right_mul_map_eq_pi_toLin, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

def transposeLinearEquivAlt : (Fin N → Fin N → ℂ) ≃ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z i j := Z j i
  invFun Z i j := Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `Z`. Use function extensionality and compare the values at `i j`. Use `show (∑ k, g i k * Z k j) = ∑ k, Z k j * g i k`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem left_mul_map_eq_transpose_conj (g : Matrix (Fin N) (Fin N) ℂ) :
    leftMulLinearMap g = (transposeLinearEquivAlt (N := N)).toLinearMap ∘ₗ rightMulLinear gᵀ ∘ₗ
      (transposeLinearEquivAlt (N := N)).symm.toLinearMap := by
  apply LinearMap.ext; intro Z; funext i j
  show (∑ k, g i k * Z k j) = ∑ k, Z k j * g i k
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Rewrite using `[left_mul_map_eq_transpose_conj, LinearMap.det_conj, det_right_mul_map_eq_det_pow, Matrix.det_transpose]`.
-/
theorem det_left_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (leftMulLinearMap g) = g.det ^ N := by
  rw [left_mul_map_eq_transpose_conj, LinearMap.det_conj, det_right_mul_map_eq_det_pow, Matrix.det_transpose]

/- English proof (translation)
Rewrite using `[LinearMap.det_restrictScalars, hf, map_pow, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]`.
-/
theorem real_det_restrictScalars (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ)
    (hf : LinearMap.det f = d ^ N) :
    LinearMap.det (f.restrictScalars ℝ) = (‖d‖ ^ 2) ^ N := by
  rw [LinearMap.det_restrictScalars, hf, map_pow, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/- English proof (translation)
Rewrite using `[_root_.zpow_neg, ← pow_mul, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]`.
-/
theorem zpow_neg_two_mul_eq_inv_sq_pow (x : ℝ) : x ^ (-(2 * (N : ℤ))) = ((x ^ 2) ^ N)⁻¹ := by
  rw [_root_.zpow_neg, ← pow_mul, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

/- English proof (translation)
Establish `hdet` using `real_det_restrictScalars f d hf`. Establish `hne : LinearMap.det (f.restrictScalars ℝ) ≠ 0`. Rewrite using `[hdet]`. Conclude with `pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))`. Use `haveI := matrix_space_volume_isAddHaar N`.

Rewrite using `[Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, hdet, zpow_neg_two_mul_eq_inv_sq_pow, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))]`.
-/
theorem map_volume_of_det_eq_pow (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ) (hd : d ≠ 0)
    (hf : LinearMap.det f = d ^ N) :
    Measure.map (f.restrictScalars ℝ) volume = ENNReal.ofReal (‖d‖ ^ (-(2 * (N : ℤ)))) • volume := by
  have hdet := real_det_restrictScalars f d hf
  have hne : LinearMap.det (f.restrictScalars ℝ) ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))
  haveI := matrix_space_volume_isAddHaar N
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, hdet, zpow_neg_two_mul_eq_inv_sq_pow,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))]

/- English proof (translation)
The claim follows from `Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))`.
-/
private theorem fdV0_det_cont_lemma (N : ℕ) :
    Continuous (fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det) :=
  Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))

/- English proof (translation)
Establish `h : gmDens N = fun Z => ENNReal.ofReal (((‖(Matrix.of Z).det‖ ^ 2) ^ N)⁻¹)`. Use function extensionality and compare the values at `Z`. Simplify using `only [gmDens, zpow_neg_two_mul_eq_inv_sq_pow]`. Rewrite using `[h]`. Conclude with `ENNReal.measurable_ofReal.comp (((fdV0_det_cont_lemma N).norm.measurable.pow_const 2).pow_const N).inv`.
-/
theorem measurable_gl_density : Measurable (gmDens N) := by
  have h : gmDens N = fun Z => ENNReal.ofReal (((‖(Matrix.of Z).det‖ ^ 2) ^ N)⁻¹) := by
    funext Z; simp only [gmDens, zpow_neg_two_mul_eq_inv_sq_pow]
  rw [h]
  exact ENNReal.measurable_ofReal.comp
    (((fdV0_det_cont_lemma N).norm.measurable.pow_const 2).pow_const N).inv

/- English proof (translation)
Unfold `gmDens`. Rewrite using `[Equiv.apply_symm_apply, Matrix.det_mul, norm_mul, mul_zpow, ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]`.
-/
theorem gl_density_left_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (g * Matrix.of Z)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

/- English proof (translation)
Unfold `gmDens`. Rewrite using `[Equiv.apply_symm_apply, Matrix.det_mul, mul_comm (Matrix.of Z).det, norm_mul, mul_zpow, ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]`.
-/
theorem gl_density_right_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (Matrix.of Z * g)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, mul_comm (Matrix.of Z).det, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

/- English proof (translation)
Use extensionality with `s hs`. Establish `hD` using `measurable_gl_density (N := N)`. Establish `key : ∀ Z, gmDens N Z = c⁻¹ * gmDens N (φ Z)`. Introduce `Z`. Rewrite using `[hd, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]`.

Establish `h1 : ∫⁻ Z in φ ⁻¹' s, gmDens N Z = c⁻¹ * ∫⁻ Z in φ ⁻¹' s, gmDens N (φ Z)`. Rewrite using `[← lintegral_const_mul c⁻¹ (f := fun Z => gmDens N (φ Z)) (hD.comp hφ)]`. Conclude with `lintegral_congr fun Z => key Z`. Simplify using `only [gmMeas]`. Rewrite using `[Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs, h1, ← setLIntegral_map hs hD hφ, hmap, Measure.restrict_smul, lintegral_smul_measure]`.

Apply the tactic sequence `try simp only [smul_eq_mul]`. Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]`.
-/
theorem map_gaussian_measure_eq {φ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)} (hφ : Measurable φ) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hmap : Measure.map φ volume = c • volume)
    (hd : ∀ Z, gmDens N (φ Z) = c * gmDens N Z) : Measure.map φ (gmMeas N) = gmMeas N := by
  ext s hs
  have hD := measurable_gl_density (N := N)
  have key : ∀ Z, gmDens N Z = c⁻¹ * gmDens N (φ Z) := by
    intro Z; rw [hd, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have h1 : ∫⁻ Z in φ ⁻¹' s, gmDens N Z = c⁻¹ * ∫⁻ Z in φ ⁻¹' s, gmDens N (φ Z) := by
    rw [← lintegral_const_mul c⁻¹ (f := fun Z => gmDens N (φ Z)) (hD.comp hφ)]
    exact lintegral_congr fun Z => key Z
  simp only [gmMeas]
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs, h1,
    ← setLIntegral_map hs hD hφ, hmap, Measure.restrict_smul, lintegral_smul_measure]
  try simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

/- English proof (translation)
Conclude with `(ENNReal.ofReal_pos.mpr (zpow_pos (norm_pos_iff.mpr hg) _)).ne'`.
-/
theorem ofReal_norm_det_zpow_ne_zero (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (zpow_pos (norm_pos_iff.mpr hg) _)).ne'

/- English proof (translation)
The claim follows from `map_volume_of_det_eq_pow (leftMulLinearMap g) g.det hg (det_left_mul_map_eq_det_pow g)`.
-/
theorem map_volume_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (leftMulLinearMap g) g.det hg (det_left_mul_map_eq_det_pow g)

/- English proof (translation)
The claim follows from `map_volume_of_det_eq_pow (rightMulLinear g) g.det hg (det_right_mul_map_eq_det_pow g)`.
-/
theorem map_volume_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (rightMulLinear g) g.det hg (det_right_mul_map_eq_det_pow g)

/- English proof (translation)
Establish `hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z))` using `(leftMulLinearMap g).continuous_of_finiteDimensional.measurable`. Conclude with `map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_left g hg) (gl_density_left_mul g)`.
-/
theorem gmMeas_map_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) :=
    (leftMulLinearMap g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_left g hg)
    (gl_density_left_mul g)

/- English proof (translation)
Establish `hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g))` using `(rightMulLinear g).continuous_of_finiteDimensional.measurable`. Conclude with `map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_right g hg) (gl_density_right_mul g)`.
-/
theorem gmMeas_map_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) :=
    (rightMulLinear g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_right g hg)
    (gl_density_right_mul g)

/- English proof (translation)
Establish `hcont : ContinuousOn (fun Z : Fin N → Fin N → ℂ => ‖(Matrix.of Z).det‖ ^ (-(2 * (N : ℤ)))) K` using `((fdV0_det_cont_lemma N).norm.continuousOn).zpow₀ _ fun Z hZ => Or.inl (norm_ne_zero_iff.mpr (hK0 Z hZ))`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hcont`. Establish `hDle : ∀ Z ∈ K, gmDens N Z ≤ ENNReal.ofReal C` using `fun Z hZ => ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC Z hZ))`. Simplify using `only [gmMeas]`. Rewrite using `[withDensity_apply _ hK.measurableSet]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gmMeas_compact_lt_top (K : Set (Fin N → Fin N → ℂ)) (hK : IsCompact K)
    (hK0 : ∀ Z ∈ K, (Matrix.of Z).det ≠ 0) : gmMeas N K < ⊤ := by
  have hcont : ContinuousOn
      (fun Z : Fin N → Fin N → ℂ => ‖(Matrix.of Z).det‖ ^ (-(2 * (N : ℤ)))) K :=
    ((fdV0_det_cont_lemma N).norm.continuousOn).zpow₀ _
      fun Z hZ => Or.inl (norm_ne_zero_iff.mpr (hK0 Z hZ))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hDle : ∀ Z ∈ K, gmDens N Z ≤ ENNReal.ofReal C := fun Z hZ =>
    ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC Z hZ))
  simp only [gmMeas]
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ Z in K, gmDens N Z ≤ ∫⁻ _ in K, ENNReal.ofReal C :=
        lintegral_mono_ae (ae_restrict_of_forall_mem hK.measurableSet hDle)
    _ = ENNReal.ofReal C * volume K := setLIntegral_const K _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
