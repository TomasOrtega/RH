import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.UpperHalfPlaneCoordinates

def Ψ (x y : ℝ) : ℂ := (y : ℂ) * (x + Complex.I)

/- English proof (translation)
Unfold `Ψ`. Use `fun_prop`.
-/
theorem cont_Ψ : Continuous (fun p : ℝ × ℝ => Ψ p.1 p.2) := by
  unfold Ψ; fun_prop

/- English proof (translation)
Establish `hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / |p.2|) * G (Ψ p.1 p.2))`. Use `Measurable.mul ?_ (hG.comp cont_Ψ.measurable)` and prove the remaining obligations. Conclude with `ENNReal.measurable_ofReal.comp (by fun_prop)`. Rewrite using `[lintegral_lintegral_swap hm.aemeasurable]`. Establish `hF : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2) * G z)`.

Use `Measurable.mul ?_ hG` and prove the remaining obligations. Conclude with `ENNReal.measurable_ofReal.comp (by fun_prop)`. Establish `hR : ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z = ∫⁻ y : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (1 / y ^ 2) * G ((u : ℂ) + y * Complex.I)`. Rewrite using `[← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`. Rewrite using `[Measure.volume_eq_prod, lintegral_prod_symm]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Use `congr 1`. Use function extensionality and compare the values at `u`. Simplify using `only [Complex.measurableEquivRealProd]`.

Use `congr 2`. Conclude with `Complex.mk_eq_add_mul_I u y`. Conclude with `(hF.comp (MeasurableEquiv.measurable _)).aemeasurable`. Rewrite using `[hR]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Establish `hmx : Measurable (fun x : ℝ => G (Ψ x y))` using `hG.comp (cont_Ψ.comp (Continuous.prodMk continuous_id continuous_const)).measurable`. Rewrite using `[lintegral_const_mul _ hmx]`. Establish `hmu : Measurable (fun u : ℝ => G ((u : ℂ) + y * Complex.I))` using `hG.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + y * Complex.I)).measurable`. Rewrite using `[lintegral_const_mul _ hmu]`.

Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Simplify using the standard rewrite rules. Establish `hsc : ∫⁻ x, G (Ψ x y) = ENNReal.ofReal |y⁻¹| * ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use function extensionality and compare the values at `x`. Use `congr 1`. Simplify using `only [Ψ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) ∂(Measure.map (fun x => y * x) volume) := (lintegral_map hmu (measurable_const_mul y)).symm`. Use `_ = _ := by rw [Real.map_volume_mul_left hy, lintegral_smul_measure, smul_eq_mul]`. Rewrite using `[hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]`. Rewrite using `[show 1 / |y| * |y⁻¹| = 1 / y ^ 2 by`. Rewrite using `[abs_inv, one_div, one_div, ← mul_inv, ← pow_two, sq_abs]]`.
-/
theorem key (G : ℂ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y)
      = ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / |p.2|) * G (Ψ p.1 p.2)) := by
    refine Measurable.mul ?_ (hG.comp cont_Ψ.measurable)
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hF : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2) * G z) := by
    refine Measurable.mul ?_ hG
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hR : ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z
      = ∫⁻ y : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (1 / y ^ 2) * G ((u : ℂ) + y * Complex.I) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    rw [Measure.volume_eq_prod, lintegral_prod_symm]
    · congr 1; funext y; congr 1; funext u
      simp only [Complex.measurableEquivRealProd]
      congr 2
      exact Complex.mk_eq_add_mul_I u y
    · exact (hF.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [hR]
  congr 1; funext y
  have hmx : Measurable (fun x : ℝ => G (Ψ x y)) :=
    hG.comp (cont_Ψ.comp (Continuous.prodMk continuous_id continuous_const)).measurable
  rw [lintegral_const_mul _ hmx]
  have hmu : Measurable (fun u : ℝ => G ((u : ℂ) + y * Complex.I)) :=
    hG.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + y * Complex.I)).measurable
  rw [lintegral_const_mul _ hmu]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hsc : ∫⁻ x, G (Ψ x y) = ENNReal.ofReal |y⁻¹| * ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) := by
      calc ∫⁻ x, G (Ψ x y) = ∫⁻ x : ℝ, G (((y * x : ℝ) : ℂ) + y * Complex.I) := by
            congr 1; funext x; congr 1; simp only [Ψ]; push_cast; ring
        _ = ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) ∂(Measure.map (fun x => y * x) volume) :=
            (lintegral_map hmu (measurable_const_mul y)).symm
        _ = _ := by rw [Real.map_volume_mul_left hy, lintegral_smul_measure, smul_eq_mul]
    rw [hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 / |y| * |y⁻¹| = 1 / y ^ 2 by
      rw [abs_inv, one_div, one_div, ← mul_inv, ← pow_two, sq_abs]]

def ν0 : Measure P := Measure.comap Subtype.val volume

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vol_eq : (volume : Measure P) = ν0.withDensity (fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := rfl

/- English proof (translation)
The claim follows from `(isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet`.
-/
theorem hS : MeasurableSet {z : ℂ | z.im ≠ 0} :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet

/- English proof (translation)
Unfold `pt`. Conclude with `Continuous.subtype_mk (by fun_prop) _`.
-/
theorem cont_pt : Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) := by
  unfold pt
  exact Continuous.subtype_mk (by fun_prop) _

/- English proof (translation)
Establish `hemb : MeasurableEmbedding (Subtype.val : P → ℂ)` using `MeasurableEmbedding.subtype_coe hS`. Establish `hY : MeasurableSet {y : ℝ | y ≠ 0}` using `(measurableSet_singleton 0).compl`. Establish `hembY : MeasurableEmbedding (Subtype.val : {y : ℝ // y ≠ 0} → ℝ)` using `MeasurableEmbedding.subtype_coe hY`. Establish `: SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume)` using `SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by rw [hembY.map_comap]; infer_instance)`. Use `⟨cont_pt.measurable, ?_⟩` and prove the remaining obligations.

Use extensionality with `s hs`. Use `set G : ℂ → ℝ≥0∞ := (Subtype.val '' s).indicator 1 with hGdef`. Establish `hGm : Measurable G` using `measurable_one.indicator (hemb.measurableSet_image.2 hs)`. Establish `hGv : ∀ z : P, G z.1 = s.indicator 1 z`. Introduce `z`.

Establish `hz : z.1 ∈ Subtype.val '' s ↔ z ∈ s` using `⟨fun ⟨w, hw, e⟩ => (Subtype.ext e : w = z) ▸ hw, fun h => ⟨z, h, rfl⟩⟩`. Rewrite using `[hGdef]`. Distinguish the cases in `h : z ∈ s`. Rewrite using `[Set.indicator_of_mem (hz.2 h), Set.indicator_of_mem h]`. Both sides reduce to the same expression.

Rewrite using `[Set.indicator_of_notMem (mt hz.1 h), Set.indicator_of_notMem h]`. Rewrite using `[Measure.map_apply cont_pt.measurable hs, ← lintegral_indicator_one (cont_pt.measurable hs)]`. Establish `e1 : ∀ p : ℝ × {y : ℝ // y ≠ 0}, ((fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1 p = G (Ψ p.1 p.2.1)`. Introduce `p`. Rewrite using `[show Ψ p.1 p.2.1 = (pt p.1 p.2.1 p.2.2).1 from rfl, hGv]`.

Both sides reduce to the same expression. Repeatedly rewrite using `[e1]`. Establish `hGΨ : Measurable (fun p : ℝ × {y : ℝ // y ≠ 0} => G (Ψ p.1 p.2.1))` using `hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd))).measurable`. Rewrite using `[lintegral_prod _ hGΨ.aemeasurable]`. Establish `e2 : ∀ x : ℝ, ∫⁻ y, G (Ψ x y.1) ∂((Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|)) = ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y)`.

Introduce `x`. Establish `hd : Measurable (fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))` using `(by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (1 / |y|))).comp measurable_subtype_coe`. Establish `hg : Measurable (fun y : {y : ℝ // y ≠ 0} => G (Ψ x y.1))` using `hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_const continuous_subtype_val)).measurable`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hd hg]`. Use `lintegral_subtype_comap (μ := (volume : Measure ℝ)) hY (fun y => ENNReal.ofReal (1 / |y|) * G (Ψ x y))` as an intermediate fact.

Rewrite `this` using `[show ({y : ℝ | y ≠ 0} : Set ℝ) = {0}ᶜ from rfl, restrict_compl_singleton]`. Conclude with `this`. Repeatedly rewrite using `[e2]`. Rewrite using `[key G hGm]`. Establish `hv : (volume : Measure P) s = ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0`.

Rewrite using `[vol_eq, withDensity_apply _ hs, ← lintegral_indicator hs]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Apply the tactic sequence `rw [hGv]; by_cases h : z ∈ s <;> simp [Set.indicator, h]`. Establish `hv2 : ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0 = ∫⁻ z in {z : ℂ | z.im ≠ 0}, ENNReal.ofReal (1 / z.im ^ 2) * G z` using `lintegral_subtype_comap hS (fun z => ENNReal.ofReal (1 / z.im ^ 2) * G z)`.

Rewrite using `[hv, hv2, ← lintegral_indicator hS]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Distinguish the cases in `h : z.im ≠ 0`. Simplify using `[Set.indicator, h]`.

Simplify using `[Set.indicator, not_not.1 h]`.
-/
theorem meas_pres : MeasurePreserving (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)
    ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity
      fun y => ENNReal.ofReal (1 / |y.1|))) volume := by
  have hemb : MeasurableEmbedding (Subtype.val : P → ℂ) := MeasurableEmbedding.subtype_coe hS
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hembY : MeasurableEmbedding (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) := MeasurableEmbedding.subtype_coe hY
  have : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by rw [hembY.map_comap]; infer_instance)
  refine ⟨cont_pt.measurable, ?_⟩
  ext s hs
  set G : ℂ → ℝ≥0∞ := (Subtype.val '' s).indicator 1 with hGdef
  have hGm : Measurable G := measurable_one.indicator (hemb.measurableSet_image.2 hs)
  have hGv : ∀ z : P, G z.1 = s.indicator 1 z := by
    intro z
    have hz : z.1 ∈ Subtype.val '' s ↔ z ∈ s :=
      ⟨fun ⟨w, hw, e⟩ => (Subtype.ext e : w = z) ▸ hw, fun h => ⟨z, h, rfl⟩⟩
    rw [hGdef]
    by_cases h : z ∈ s
    · rw [Set.indicator_of_mem (hz.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hz.1 h), Set.indicator_of_notMem h]
  rw [Measure.map_apply cont_pt.measurable hs, ← lintegral_indicator_one (cont_pt.measurable hs)]
  have e1 : ∀ p : ℝ × {y : ℝ // y ≠ 0},
      ((fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1 p = G (Ψ p.1 p.2.1) := by
    intro p
    rw [show Ψ p.1 p.2.1 = (pt p.1 p.2.1 p.2.2).1 from rfl, hGv]
    rfl
  simp_rw [e1]
  have hGΨ : Measurable (fun p : ℝ × {y : ℝ // y ≠ 0} => G (Ψ p.1 p.2.1)) :=
    hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp continuous_snd))).measurable
  rw [lintegral_prod _ hGΨ.aemeasurable]
  have e2 : ∀ x : ℝ, ∫⁻ y, G (Ψ x y.1) ∂((Measure.comap Subtype.val volume).withDensity
      fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))
      = ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y) := by
    intro x
    have hd : Measurable (fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|)) :=
      (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (1 / |y|))).comp measurable_subtype_coe
    have hg : Measurable (fun y : {y : ℝ // y ≠ 0} => G (Ψ x y.1)) :=
      hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_const continuous_subtype_val)).measurable
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hg]
    have := lintegral_subtype_comap (μ := (volume : Measure ℝ)) hY
      (fun y => ENNReal.ofReal (1 / |y|) * G (Ψ x y))
    rw [show ({y : ℝ | y ≠ 0} : Set ℝ) = {0}ᶜ from rfl, restrict_compl_singleton] at this
    exact this
  simp_rw [e2]
  rw [key G hGm]
  have hv : (volume : Measure P) s = ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0 := by
    rw [vol_eq, withDensity_apply _ hs, ← lintegral_indicator hs]
    congr 1; funext z
    rw [hGv]; by_cases h : z ∈ s <;> simp [Set.indicator, h]
  have hv2 : ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0
      = ∫⁻ z in {z : ℂ | z.im ≠ 0}, ENNReal.ofReal (1 / z.im ^ 2) * G z :=
    lintegral_subtype_comap hS (fun z => ENNReal.ofReal (1 / z.im ^ 2) * G z)
  rw [hv, hv2, ← lintegral_indicator hS]
  congr 1; funext z
  by_cases h : z.im ≠ 0
  · simp [Set.indicator, h]
  · simp [Set.indicator, not_not.1 h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, y, hy⟩ ⟨x', y', hy'⟩ h`. Establish `h' : (y : ℂ) * (x + Complex.I) = (y' : ℂ) * (x' + Complex.I)` using `congrArg Subtype.val h`. Establish `him` using `congrArg Complex.im h'`. Establish `hre` using `congrArg Complex.re h'`.

Simplify using `at him hre`. Substitute `him` using the available equality. Establish `: x = x'` using `mul_left_cancel₀ hy hre`. Substitute `this` using the available equality. Both sides reduce to the same expression.

Introduce and unpack `⟨z, hz⟩`. Use `⟨(z.re / z.im, ⟨z.im, hz⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (z.im : ℂ) * ((z.re / z.im : ℝ) + Complex.I) = z`. Apply the tactic sequence `apply Complex.ext <;> simp; field_simp`.
-/
theorem bij : Function.Bijective (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) := by
  constructor
  · rintro ⟨x, y, hy⟩ ⟨x', y', hy'⟩ h
    have h' : (y : ℂ) * (x + Complex.I) = (y' : ℂ) * (x' + Complex.I) := congrArg Subtype.val h
    have him := congrArg Complex.im h'
    have hre := congrArg Complex.re h'
    simp at him hre
    subst him
    have : x = x' := mul_left_cancel₀ hy hre
    subst this; rfl
  · rintro ⟨z, hz⟩
    refine ⟨(z.re / z.im, ⟨z.im, hz⟩), ?_⟩
    apply Subtype.ext
    show (z.im : ℂ) * ((z.re / z.im : ℝ) + Complex.I) = z
    apply Complex.ext <;> simp; field_simp

end UpperTheory.Esk.UpperHalfPlaneCoordinates

/- English proof (translation)
Assemble the required witnesses or components as `⟨UpperTheory.Esk.UpperHalfPlaneCoordinates.meas_pres, UpperTheory.Esk.UpperHalfPlaneCoordinates.bij, UpperTheory.Esk.UpperHalfPlaneCoordinates.cont_pt⟩`.
-/
theorem UpperTheory.Esk.upper_half_plane_measure_coordinates : UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates :=
  ⟨UpperTheory.Esk.UpperHalfPlaneCoordinates.meas_pres, UpperTheory.Esk.UpperHalfPlaneCoordinates.bij, UpperTheory.Esk.UpperHalfPlaneCoordinates.cont_pt⟩
