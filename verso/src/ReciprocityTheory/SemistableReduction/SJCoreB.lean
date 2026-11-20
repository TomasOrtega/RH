import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.SJCoreA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

/- English proof (translation)
Rewrite using `[Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Rewrite using `[← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]`.
-/
theorem integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]

/- English proof (translation)
Rewrite using `[Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Establish `h2` using `(integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h`. Use `h2.congr (Filter.Eventually.of_forall fun r => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]`.
-/
theorem integrable_volumeIoiPow {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]

/- English proof (translation)
Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_fin]`.
-/
theorem finrank_euclidean_complex (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

/- English proof (translation)
Establish `hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0` using `norm_ne_zero_iff.mpr x.2`. Simplify using `[homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]`.
-/
private theorem homeomorphUnitSphereProd_smul_eq {n : ℕ} (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) :
    ((homeomorphUnitSphereProd _ x).2 : ℝ) •
      ((homeomorphUnitSphereProd _ x).1 : EuclideanSpace ℂ (Fin n)) = x := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]

/- English proof (translation)
Rewrite using `[← (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp (homeomorphUnitSphereProd _).measurableEmbedding (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]`. Simplify using `only [homeomorphUnitSphereProd_smul_eq]`. Rewrite using `[integral_subtype_comap (measurableSet_singleton 0).compl (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]`. Use `haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)`. Rewrite using `[Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]`.
-/
theorem integral_polar {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp
      (homeomorphUnitSphereProd _).measurableEmbedding
      (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]
  simp only [homeomorphUnitSphereProd_smul_eq]
  rw [integral_subtype_comap (measurableSet_singleton 0).compl
    (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  rw [Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from
    ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]

/- English proof (translation)
Rewrite using `[← (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb (homeomorphUnitSphereProd _).measurableEmbedding]`. Establish `h2` using `(integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn`. Use `h2.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]`.
-/
theorem integrable_polar (n : ℕ) {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb
      (homeomorphUnitSphereProd _).measurableEmbedding]
  have h2 := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton
    (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]

def conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ star (WithLp.ofLp c i))

/- English proof (translation)
Simplify using `[conjVec, PiLp.inner_apply, mul_comm]`.
-/
theorem inner_conjVec {n : ℕ} (c x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (conjVec c) x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
  simp [conjVec, PiLp.inner_apply, mul_comm]

/- English proof (translation)
Simplify using `[conjVec, EuclideanSpace.norm_eq]`.
-/
theorem norm_conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : ‖conjVec c‖ = ‖c‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

/- English proof (translation)
Set `K : Submodule ℝ (EuclideanSpace ℂ (Fin n))` to `(LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ`. Establish `hK : K ≠ ⊤`. Introduce `h`. Establish `hm : conjVec c ∈ K` using `h ▸ Submodule.mem_top`. Establish `hm' : inner ℂ (conjVec c) (conjVec c) = 0` using `hm`.

Rewrite `hm'` using `[inner_self_eq_zero]`. Conclude with `hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])`. Establish `hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, spherePoint, inner_conjVec]`.

Establish `hs : MeasurableSet {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0}` using `(isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet`. Rewrite using `[hset, Measure.toSphere_apply' _ hs, measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]`. Introduce and unpack `_ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩`. Conclude with `K.smul_mem t hz`.
-/
theorem sphere_linear_zero_null {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    (LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ
  have hK : K ≠ ⊤ := by
    intro h
    have hm : conjVec c ∈ K := h ▸ Submodule.mem_top
    have hm' : inner ℂ (conjVec c) (conjVec c) = 0 := hm
    rw [inner_self_eq_zero] at hm'
    exact hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])
  have hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} =
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, spherePoint, inner_conjVec]
  have hs : MeasurableSet
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [hset, Measure.toSphere_apply' _ hs,
    measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]
  rintro _ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩
  exact K.smul_mem t hz

def gaussLogC (a : ℝ) : ℝ := ∫ z : ℂ, log (a * ‖z‖) * exp (-‖z‖ ^ 2)

def gaussOneC : ℝ := ∫ z : ℂ, exp (-‖z‖ ^ 2)

/- English proof (translation)
The claim follows from `integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs`.
-/
private theorem integrableOn_rpow_mul_exp_neg_sq_Ioi (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ ↦ y ^ s * exp (-1 * y ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs

/- English proof (translation)
Use `(integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_` and prove the remaining obligations. Establish `hd : Module.finrank ℝ ℂ - 1 = 1` using `by simp [Complex.finrank_real_complex]`. Simplify using `only [hd, pow_one, smul_eq_mul]`. Use `(integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi` and prove the remaining obligations.
-/
theorem integrable_gaussOneC : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun
    (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi

/- English proof (translation)
Establish `h1 : log y ≤ 2 * y ^ (1 / 2 : ℝ)`. Use `Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : -log y ≤ 2 * y ^ (-1 / 2 : ℝ)`. Use `Real.log_le_rpow_div (inv_pos.mpr hy).le (show (0 : ℝ) < 1 / 2 by norm_num)` as an intermediate fact.

Rewrite `this` using `[Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le]`. Establish `e : (-(1 / 2 : ℝ)) = -1 / 2` using `by norm_num`. Rewrite `this` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `p1` using `Real.rpow_nonneg hy.le (1 / 2 : ℝ)`.

Establish `p2` using `Real.rpow_nonneg hy.le (-1 / 2 : ℝ)`. Establish `habs : |log y| ≤ 2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ)` using `abs_le.mpr ⟨by linarith, by linarith⟩`. Establish `hlog : |log (a * y)| ≤ |log a| + |log y|`. Rewrite using `[Real.log_mul ha.ne' hy.ne']`. Conclude with `abs_add_le _ _`.

Establish `e1 : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ)`. Rewrite using `[show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]`. Establish `e2 : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ)`. Rewrite using `[show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hy, Real.rpow_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.rpow_one]`. Take the linear combination `2 * e1 + 2 * e2`.
-/
private theorem mul_abs_log_mul_le {a : ℝ} (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    y * |log (a * y)| ≤ |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
  have h1 : log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have h2 : -log y ≤ 2 * y ^ (-1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (inv_pos.mpr hy).le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
    have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [e] at this
    linarith
  have p1 := Real.rpow_nonneg hy.le (1 / 2 : ℝ)
  have p2 := Real.rpow_nonneg hy.le (-1 / 2 : ℝ)
  have habs : |log y| ≤ 2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hlog : |log (a * y)| ≤ |log a| + |log y| := by
    rw [Real.log_mul ha.ne' hy.ne']; exact abs_add_le _ _
  have e1 : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  have e2 : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hy, Real.rpow_one]
  calc y * |log (a * y)| ≤ y * (|log a| + (2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ))) := by
        gcongr; exact hlog.trans (by linarith)
    _ = |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]; linear_combination 2 * e1 + 2 * e2

/- English proof (translation)
Use `(integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ log (a * y) * exp (-y ^ 2))).mpr ?_` and prove the remaining obligations. Establish `hd : Module.finrank ℝ ℂ - 1 = 1` using `by simp [Complex.finrank_real_complex]`. Simplify using `only [hd, pow_one, smul_eq_mul]`. Establish `hg : IntegrableOn (fun y : ℝ ↦ (|log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ)) * exp (-1 * y ^ 2)) (Ioi 0)`. Use `(((integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).const_mul |log a|).add ((integrableOn_rpow_mul_exp_neg_sq_Ioi (3 / 2) (by norm_num)).const_mul 2)).add ((integrableOn_rpow_mul_exp_neg_sq_Ioi (1 / 2) (by norm_num)).const_mul 2)` as an intermediate fact.

Use `this.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ ↦ ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `Integrable.mono' hg (by fun_prop) ?_` and prove the remaining obligations. Use `ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_` and prove the remaining obligations.

Establish `hy' : (0 : ℝ) < y` using `hy`. Rewrite using `[norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy', abs_of_pos (exp_pos _), neg_one_mul, ← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (mul_abs_log_mul_le ha y hy') (exp_pos _).le`.
-/
theorem integrable_gaussLogC {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ log (a * ‖z‖) * exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ log (a * y) * exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  have hg : IntegrableOn (fun y : ℝ ↦ (|log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) +
      2 * y ^ (1 / 2 : ℝ)) * exp (-1 * y ^ 2)) (Ioi 0) := by
    have := (((integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).const_mul |log a|).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (3 / 2) (by norm_num)).const_mul 2)).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (1 / 2) (by norm_num)).const_mul 2)
    refine this.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine Integrable.mono' hg (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_
  have hy' : (0 : ℝ) < y := hy
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hy', abs_of_pos (exp_pos _), neg_one_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_abs_log_mul_le ha y hy') (exp_pos _).le

end ReciprocityTheory.MultiplicativeHeights
