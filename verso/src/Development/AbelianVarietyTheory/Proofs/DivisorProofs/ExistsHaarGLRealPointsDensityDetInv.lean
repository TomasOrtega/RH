import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace GlobalTheory.GLHaar

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmul_apply (y x : Lie E a) : lmul y x = toL (Matrix.of y * Matrix.of x) := rfl

/- English proof (translation)
Use extensionality with `z : 1`. Simplify using `only [ContinuousLinearMap.comp_apply, lmul_apply]`. Simplify using `[Matrix.mul_assoc]`.
-/
theorem lmul_lmul (y x : Lie E a) : lmul (lmul y x) = (lmul y).comp (lmul x) := by
  ext z : 1
  simp only [ContinuousLinearMap.comp_apply, lmul_apply]
  simp [Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `z : 1`. Simplify using `[lmul_apply]`.
-/
theorem lmul_one : lmul (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = ContinuousLinearMap.id ℝ _ := by
  ext z : 1
  simp [lmul_apply]

def dL (x : Lie E a) : ℝ := LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)

/- English proof (translation)
Unfold `dL`. Rewrite using `[lmul_lmul]`. Conclude with `LinearMap.det_comp (lmul y : Lie E a →ₗ[ℝ] Lie E a) (lmul x : Lie E a →ₗ[ℝ] Lie E a)`.
-/
theorem dL_mul (y x : Lie E a) : dL (lmul y x) = dL y * dL x := by
  unfold dL
  rw [lmul_lmul]
  exact LinearMap.det_comp (lmul y : Lie E a →ₗ[ℝ] Lie E a) (lmul x : Lie E a →ₗ[ℝ] Lie E a)

/- English proof (translation)
Use extensionality with `z : 1`. Conclude with `Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)`.
-/
theorem lmul_add (x y : Lie E a) : lmul (x + y) = lmul x + lmul y := by
  ext z : 1
  exact Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)

/- English proof (translation)
Use extensionality with `z : 1`. Conclude with `Matrix.smul_mul c (Matrix.of x) (Matrix.of z)`.
-/
theorem lmul_smul (c : ℝ) (x : Lie E a) : lmul (c • x) = c • lmul x := by
  ext z : 1
  exact Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

def lmulL : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' := lmul_add
  map_smul' := lmul_smul

/- English proof (translation)
The claim follows from `ContinuousLinearMap.continuous_det.comp (LinearMap.continuous_of_finiteDimensional (lmulL (E := E) (a := a)))`.
-/
theorem continuous_dL : Continuous (dL (E := E) (a := a)) :=
  ContinuousLinearMap.continuous_det.comp (LinearMap.continuous_of_finiteDimensional (lmulL (E := E) (a := a)))

open scoped ENNReal NNReal

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def jG (y : glG E a) : Lie E a := toL y.1.val

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jG_mul (g y : glG E a) : jG (g * y) = lmul (jG g) (jG y) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jG_one : jG (1 : glG E a) = toL 1 := rfl

/- English proof (translation)
Establish `hO : IsOpen ((glG E a : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Set (Matrix (Fin a) (Fin a) (Cinf E))ˣ)`. Simplify using the standard rewrite rules. Conclude with `GlobalTheory.CuspQuot.isOpenEmbedding_val.comp hO.isOpenEmbedding_subtypeVal`.
-/
theorem isOpenEmbedding_jG : Topology.IsOpenEmbedding (jG (E := E) (a := a)) := by
  have hO : IsOpen ((glG E a : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Set (Matrix (Fin a) (Fin a) (Cinf E))ˣ) := by
    simp
  exact GlobalTheory.CuspQuot.isOpenEmbedding_val.comp hO.isOpenEmbedding_subtypeVal

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `val_mem_invSet y.1`. Introduce `hx`.

Conclude with `⟨⟨hx.unit, Subgroup.mem_top _⟩, hx.unit_spec⟩`.
-/
theorem range_jG : Set.range (jG (E := E) (a := a)) = invSet E a := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact val_mem_invSet y.1
  · intro hx
    exact ⟨⟨hx.unit, Subgroup.mem_top _⟩, hx.unit_spec⟩

/- English proof (translation)
Rewrite using `[← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, mul_inv_cancel, jG_one, lmul_one]`. Both sides reduce to the same expression.
-/
theorem lmul_jG_inv (g : glG E a) (x : Lie E a) : lmul (jG g) (lmul (jG g⁻¹) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, mul_inv_cancel, jG_one, lmul_one]
  rfl

/- English proof (translation)
Rewrite using `[← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, inv_mul_cancel, jG_one, lmul_one]`. Both sides reduce to the same expression.
-/
theorem lmul_inv_jG (g : glG E a) (x : Lie E a) : lmul (jG g⁻¹) (lmul (jG g) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, inv_mul_cancel, jG_one, lmul_one]
  rfl

/- English proof (translation)
Unfold `dL`. Rewrite using `[lmul_one]`. Conclude with `LinearMap.det_id`.
-/
theorem dL_one : dL (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1 := by
  unfold dL
  rw [lmul_one]
  exact LinearMap.det_id

/- English proof (translation)
Introduce `h`. Establish `e` using `dL_mul (jG g) (jG g⁻¹)`. Rewrite `e` using `[← jG_mul, mul_inv_cancel, jG_one, dL_one, h, zero_mul]`. Conclude with `one_ne_zero e`.
-/
theorem dL_jG_ne (g : glG E a) : dL (jG g) ≠ 0 := by
  intro h
  have e := dL_mul (jG g) (jG g⁻¹)
  rw [← jG_mul, mul_inv_cancel, jG_one, dL_one, h, zero_mul] at e
  exact one_ne_zero e

/- English proof (translation)
Rewrite `hx` using `[← range_jG]`. Take `⟨g, rfl⟩` from `hx`. Conclude with `dL_jG_ne g`.
-/
theorem dL_ne_of_mem {x : Lie E a} (hx : x ∈ invSet E a) : dL x ≠ 0 := by
  rw [← range_jG] at hx
  obtain ⟨g, rfl⟩ := hx
  exact dL_jG_ne g

def rho (x : Lie E a) : ℝ≥0∞ := ENNReal.ofReal (|dL x|⁻¹)

/- English proof (translation)
The claim follows from `ENNReal.measurable_ofReal.comp (continuous_dL.abs.measurable.inv)`.
-/
theorem measurable_rho : Measurable (rho (E := E) (a := a)) :=
  ENNReal.measurable_ofReal.comp (continuous_dL.abs.measurable.inv)

/- English proof (translation)
Unfold `rho`. Rewrite using `[← ENNReal.ofReal_mul (abs_nonneg _), dL_mul, abs_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hy), one_mul]`.
-/
theorem ofReal_mul_rho (y x : Lie E a) (hy : dL y ≠ 0) :
    ENNReal.ofReal |dL y| * rho (lmul y x) = rho x := by
  unfold rho
  rw [← ENNReal.ofReal_mul (abs_nonneg _), dL_mul, abs_mul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.2 hy), one_mul]

def muG [MeasurableSpace (glG E a)] (ν : MeasureTheory.Measure (Lie E a)) : MeasureTheory.Measure (glG E a) :=
  (ν.withDensity rho).comap jG

section Haar

variable [MeasurableSpace (glG E a)] [BorelSpace (glG E a)] (ν : Measure (Lie E a)) [hν : ν.IsAddHaarMeasure]

/- English proof (translation)
The claim follows from `isOpenEmbedding_jG.measurableEmbedding`.
-/
theorem mE : MeasurableEmbedding (jG (E := E) (a := a)) := isOpenEmbedding_jG.measurableEmbedding

/- English proof (translation)
Use `set L := lmul (jG g)`. Establish `hsurj : L '' (L ⁻¹' A) = A` using `Set.image_preimage_eq A (fun x => ⟨lmul (jG g⁻¹) x, lmul_jG_inv g x⟩)`. Establish `hinj : Function.Injective L` using `fun x y h => by`. Rewrite using `[← lmul_inv_jG g x, ← lmul_inv_jG g y]`. Conclude with `congrArg _ h`.

Establish `hS : MeasurableSet (L ⁻¹' A)` using `hA.preimage L.continuous.measurable`. Rewrite using `[withDensity_apply _ hA, withDensity_apply _ hS]`. Use `conv_rhs => rw [← hsurj]`. Rewrite using `[lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hS (fun x _ => L.hasFDerivAt.hasFDerivWithinAt) hinj.injOn]`. Use `setLIntegral_congr_fun hS (fun x _ => ?_)` and prove the remaining obligations.

Conclude with `(ofReal_mul_rho (jG g) x (dL_jG_ne g)).symm`.
-/
theorem withDensity_preimage (g : glG E a) {A : Set (Lie E a)} (hA : MeasurableSet A) :
    ν.withDensity rho (lmul (jG g) ⁻¹' A) = ν.withDensity rho A := by
  set L := lmul (jG g)
  have hsurj : L '' (L ⁻¹' A) = A := Set.image_preimage_eq A (fun x => ⟨lmul (jG g⁻¹) x, lmul_jG_inv g x⟩)
  have hinj : Function.Injective L := fun x y h => by
    rw [← lmul_inv_jG g x, ← lmul_inv_jG g y]
    exact congrArg _ h
  have hS : MeasurableSet (L ⁻¹' A) := hA.preimage L.continuous.measurable
  rw [withDensity_apply _ hA, withDensity_apply _ hS]
  conv_rhs => rw [← hsurj]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hS (fun x _ => L.hasFDerivAt.hasFDerivWithinAt)
    hinj.injOn]
  refine setLIntegral_congr_fun hS (fun x _ => ?_)
  exact (ofReal_mul_rho (jG g) x (dL_jG_ne g)).symm

/- English proof (translation)
Use `⟨fun g => ?_⟩` and prove the remaining obligations. Use extensionality with `s hs`. Establish `hm : Measurable (g * · : glG E a → glG E a)` using `(continuous_const.mul continuous_id).measurable`. Rewrite using `[Measure.map_apply hm hs, muG, mE.comap_apply, mE.comap_apply]`. Establish `himg : jG '' ((g * ·) ⁻¹' s) = (lmul (jG g)) ⁻¹' (jG '' s)`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨g * y, hy, rfl⟩`. Introduce and unpack `⟨z, hz, hzx⟩`.

Use `⟨g⁻¹ * z, ?_, ?_⟩` and prove the remaining obligations. Use `show g * (g⁻¹ * z) ∈ s`. Rewrite using `[mul_inv_cancel_left]` and apply the resulting hypothesis. Use `show lmul (jG g⁻¹) (jG z) = x`. Rewrite using `[hzx, lmul_inv_jG]`.

Rewrite using `[himg]`. Conclude with `withDensity_preimage ν g (mE.measurableSet_image.2 hs)`.
-/
theorem muG_leftInv : (muG ν : Measure (glG E a)).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (g * · : glG E a → glG E a) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, muG, mE.comap_apply, mE.comap_apply]
  have himg : jG '' ((g * ·) ⁻¹' s) = (lmul (jG g)) ⁻¹' (jG '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y, hy, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨g⁻¹ * z, ?_, ?_⟩
      · show g * (g⁻¹ * z) ∈ s
        rwa [mul_inv_cancel_left]
      · show lmul (jG g⁻¹) (jG z) = x
        rw [hzx, lmul_inv_jG]
  rw [himg]
  exact withDensity_preimage ν g (mE.measurableSet_image.2 hs)

/- English proof (translation)
Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Rewrite using `[muG, mE.comap_apply]`. Establish `hK' : IsCompact (jG '' K)` using `hK.image isOpenEmbedding_jG.continuous`. Establish `hsub : jG '' K ⊆ invSet E a`. Rewrite using `[← range_jG]`.

Conclude with `Set.image_subset_range _ _`. Rewrite using `[withDensity_apply _ hK'.measurableSet]`. Establish `hc : ContinuousOn (fun x : Lie E a => |dL x|⁻¹) (jG '' K)` using `continuous_dL.abs.continuousOn.inv₀ fun x hx => abs_ne_zero.2 (dL_ne_of_mem (hsub hx))`. Conclude with `(hc.integrableOn_compact hK').lintegral_lt_top`.
-/
theorem muG_finite : IsFiniteMeasureOnCompacts (muG ν : Measure (glG E a)) := by
  refine ⟨fun K hK => ?_⟩
  rw [muG, mE.comap_apply]
  have hK' : IsCompact (jG '' K) := hK.image isOpenEmbedding_jG.continuous
  have hsub : jG '' K ⊆ invSet E a := by
    rw [← range_jG]
    exact Set.image_subset_range _ _
  rw [withDensity_apply _ hK'.measurableSet]
  have hc : ContinuousOn (fun x : Lie E a => |dL x|⁻¹) (jG '' K) :=
    continuous_dL.abs.continuousOn.inv₀ fun x hx => abs_ne_zero.2 (dL_ne_of_mem (hsub hx))
  exact (hc.integrableOn_compact hK').lintegral_lt_top

/- English proof (translation)
Use `⟨fun U hU hne => ?_⟩` and prove the remaining obligations. Rewrite using `[muG, mE.comap_apply]`. Introduce `h0`. Rewrite `h0` using `[withDensity_apply_eq_zero' measurable_rho.aemeasurable]`. Establish `he : {x | rho x ≠ 0} ∩ jG '' U = jG '' U`.

Use `Set.inter_eq_right.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, _, rfl⟩`. Conclude with `(ENNReal.ofReal_pos.2 (inv_pos.2 (abs_pos.2 (dL_jG_ne y)))).ne'`. Rewrite `h0` using `[he]`. Conclude with `(isOpenEmbedding_jG.isOpenMap U hU).measure_ne_zero ν (hne.image _) h0`.
-/
theorem muG_pos : (muG ν : Measure (glG E a)).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [muG, mE.comap_apply]
  intro h0
  rw [withDensity_apply_eq_zero' measurable_rho.aemeasurable] at h0
  have he : {x | rho x ≠ 0} ∩ jG '' U = jG '' U := by
    refine Set.inter_eq_right.2 ?_
    rintro _ ⟨y, _, rfl⟩
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 (abs_pos.2 (dL_jG_ne y)))).ne'
  rw [he] at h0
  exact (isOpenEmbedding_jG.isOpenMap U hU).measure_ne_zero ν (hne.image _) h0

/- English proof (translation)
The claim follows from `haveI := muG_leftInv ν haveI := muG_finite ν haveI := muG_pos ν { }`.
-/
theorem muG_haar : (muG ν : Measure (glG E a)).IsHaarMeasure :=
  haveI := muG_leftInv ν
  haveI := muG_finite ν
  haveI := muG_pos ν
  { }

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∫ y, Φ (jG y) ∂(muG ν) = _`. Rewrite using `[← mE.integral_map, muG, mE.map_comap, range_jG, setIntegral_eq_integral_of_forall_compl_eq_zero hΦ]`. Establish `hf : Measurable fun x : Lie E a => (|dL x|⁻¹).toNNReal` using `continuous_dL.abs.measurable.inv.real_toNNReal`. Express the relevant statement in the definitionally equal form `∫ x, Φ x ∂(ν.withDensity fun x => (((|dL x|⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞)) = _`. Rewrite using `[integral_withDensity_eq_integral_smul hf]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg _)), Complex.real_smul]`. Both sides reduce to the same expression.
-/
theorem integral_muG (Φ : Lie E a → ℂ) (hΦ : ∀ x ∉ invSet E a, Φ x = 0) :
    ∫ y, Φ (toL y.1.val) ∂(muG ν : Measure (glG E a)) =
      ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  change ∫ y, Φ (jG y) ∂(muG ν) = _
  rw [← mE.integral_map, muG, mE.map_comap, range_jG, setIntegral_eq_integral_of_forall_compl_eq_zero hΦ]
  have hf : Measurable fun x : Lie E a => (|dL x|⁻¹).toNNReal := continuous_dL.abs.measurable.inv.real_toNNReal
  change ∫ x, Φ x ∂(ν.withDensity fun x => (((|dL x|⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg _)), Complex.real_smul]
  rfl

end Haar

/- English proof (translation)
Introduce `E _ _ _ a ν hν _ _`. Conclude with `⟨muG ν, muG_haar ν, fun Φ _ hΦ => integral_muG ν Φ hΦ⟩`.
-/
theorem glHaar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ [MeasurableSpace (glG E a)] [BorelSpace (glG E a)], ∃ μ : Measure (glG E a), μ.IsHaarMeasure ∧ ∀ (Φ : Lie E a → ℂ), ContinuousOn Φ (invSet E a) → (∀ x ∉ invSet E a, Φ x = 0) → ∫ y, Φ (toL y.1.val) ∂μ = ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  intro E _ _ _ a ν hν _ _
  exact ⟨muG ν, muG_haar ν, fun Φ _ hΦ => integral_muG ν Φ hΦ⟩

end GlobalTheory.GLHaar
