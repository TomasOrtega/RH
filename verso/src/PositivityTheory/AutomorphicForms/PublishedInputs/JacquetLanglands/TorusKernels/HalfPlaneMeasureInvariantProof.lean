import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HalfPlaneMeasureLemmas

open UpperTheory.Esk

def U : Set ℂ := {z | z.im ≠ 0}

/- English proof (translation)
The claim follows from `isOpen_ne_fun Complex.continuous_im continuous_const`.
-/
theorem isOpen_U : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const

def val (z : P) : ℂ := z.1

def mk (z : ℂ) (hz : z.im ≠ 0) : P := ⟨z, hz⟩

/- English proof (translation)
The claim follows from `isOpen_U.isOpenEmbedding_subtypeVal`.
-/
theorem openEmb : Topology.IsOpenEmbedding val :=
  isOpen_U.isOpenEmbedding_subtypeVal

/- English proof (translation)
The claim follows from `openEmb.measurableEmbedding`.
-/
theorem measEmb : MeasurableEmbedding val :=
  openEmb.measurableEmbedding

def rho (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / z.im ^ 2)

def F (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / den g z

def D (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((g.val.det : ℂ) / den g z ^ 2)).restrictScalars ℝ

/- English proof (translation)
Establish `h` using `((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ) |>.add_const ((g 0 1 : ℝ) : ℂ)).div ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ) |>.add_const ((g 1 1 : ℝ) : ℂ)) (den_ne g hz)`. Use `h.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [den, id, mul_one]`. Rewrite using `[det_eq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (F g) ((g.val.det : ℂ) / den g z ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ) |>.add_const ((g 0 1 : ℝ) : ℂ)).div
    ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ) |>.add_const ((g 1 1 : ℝ) : ℂ)) (den_ne g hz)
  refine h.congr_deriv ?_
  simp only [den, id, mul_one]
  rw [det_eq]
  push_cast
  ring

/- English proof (translation)
Use `(hasDerivAt_F g hz).hasFDerivAt.restrictScalars ℝ` as an intermediate fact. Simplify `this` using `[D]`.
-/
theorem hasFDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : HasFDerivAt (F g) (D g z) z := by
  have := (hasDerivAt_F g hz).hasFDerivAt.restrictScalars ℝ
  simpa [D] using this

/- English proof (translation)
Simplify using `[D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]`.
-/
theorem det_D (g : GL (Fin 2) ℝ) (z : ℂ) :
    (D g z).det = Complex.normSq ((g.val.det : ℂ) / den g z ^ 2) := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem F_eq (g : GL (Fin 2) ℝ) (z : P) : F g (val z) = val (g • z) := rfl

/- English proof (translation)
Introduce `x hx y hy hxy`. Establish `h : g • mk x hx = g • mk y hy` using `Subtype.ext hxy`. Use `congrArg val (smul_left_cancel g h)` as an intermediate fact. Conclude with `this`.
-/
theorem injOn_F (g : GL (Fin 2) ℝ) : Set.InjOn (F g) U := by
  intro x hx y hy hxy
  have h : g • mk x hx = g • mk y hy := Subtype.ext hxy
  have := congrArg val (smul_left_cancel g h)
  exact this

/- English proof (translation)
Rewrite using `[lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS (fun x hx => (hasFDerivAt_F g (hSU hx)).hasFDerivWithinAt) ((injOn_F g).mono hSU)]`. Use `setLIntegral_congr_fun hS (fun x hx => ?_)` and prove the remaining obligations. Establish `hx' : x.im ≠ 0` using `hSU hx`. Establish `hd` using `den_ne g hx'`. Establish `hn : Complex.normSq (den g x) ≠ 0` using `by simpa using hd`.

Establish `hdet` using `g.det_ne_zero`. Rewrite using `[det_D, rho, rho, F, im_div, abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]`. Use `congr 1`. Rewrite using `[Complex.normSq_div, Complex.normSq_ofReal, map_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem key (g : GL (Fin 2) ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫⁻ x in F g '' S, rho x = ∫⁻ x in S, rho x := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x hx => (hasFDerivAt_F g (hSU hx)).hasFDerivWithinAt) ((injOn_F g).mono hSU)]
  refine setLIntegral_congr_fun hS (fun x hx => ?_)
  have hx' : x.im ≠ 0 := hSU hx
  have hd := den_ne g hx'
  have hn : Complex.normSq (den g x) ≠ 0 := by simpa using hd
  have hdet := g.det_ne_zero
  rw [det_D, rho, rho, F, im_div, abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul
    (Complex.normSq_nonneg _)]
  congr 1
  rw [Complex.normSq_div, Complex.normSq_ofReal, map_pow]
  field_simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vol_def : (volume : Measure P) = (Measure.comap val volume).withDensity fun z => rho (val z) := rfl

/- English proof (translation)
Rewrite using `[vol_def, withDensity_apply _ hs, measEmb.restrict_comap,`. Use the proof step `← measEmb.lintegral_map, measEmb.map_comap, Measure.restrict_restrict (measEmb.measurableSet_range), Set.inter_eq_right.2 (Set.image_subset_range _ _)]`.
-/
theorem vol_eq (s : Set P) (hs : MeasurableSet s) : volume s = ∫⁻ z in val '' s, rho z := by
  rw [vol_def, withDensity_apply _ hs, measEmb.restrict_comap,
← measEmb.lintegral_map, measEmb.map_comap,
    Measure.restrict_restrict (measEmb.measurableSet_range),
    Set.inter_eq_right.2 (Set.image_subset_range _ _)]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Use `⟨val (g • p), ⟨g • p, hp, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[F_eq g⁻¹ (g • p), inv_smul_smul]`. Introduce and unpack `⟨y, ⟨q, hq, rfl⟩, rfl⟩`. Use `⟨g⁻¹ • q, by rwa [smul_inv_smul], ?_⟩` and prove the remaining obligations. Rewrite using `[F_eq]`.
-/
theorem image_pre (g : GL (Fin 2) ℝ) (s : Set P) :
    val '' ((fun z : P => g • z) ⁻¹' s) = F g⁻¹ '' (val '' s) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨val (g • p), ⟨g • p, hp, rfl⟩, ?_⟩
    rw [F_eq g⁻¹ (g • p), inv_smul_smul]
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨g⁻¹ • q, by rwa [smul_inv_smul], ?_⟩
    rw [F_eq]

/- English proof (translation)
Establish `hv : Continuous (fun z : P => z.1)` using `continuous_subtype_val`. Establish `h : Continuous (fun z : P => (g • z).1)`. Express the relevant statement in the definitionally equal form `Continuous (fun z : P => num g z.1 / den g z.1)`. Use `Continuous.div ?_ ?_ (fun z => den_ne g z.2)` and prove the remaining obligations. Simplify using `only [num]`.

Use `fun_prop`. Simplify using `only [den]`. Use `fun_prop`. Conclude with `continuous_induced_rng.2 h`.
-/
theorem cont (g : GL (Fin 2) ℝ) : Continuous (fun z : P => g • z) := by
  have hv : Continuous (fun z : P => z.1) := continuous_subtype_val
  have h : Continuous (fun z : P => (g • z).1) := by
    change Continuous (fun z : P => num g z.1 / den g z.1)
    refine Continuous.div ?_ ?_ (fun z => den_ne g z.2)
    · simp only [num]; fun_prop
    · simp only [den]; fun_prop
  exact continuous_induced_rng.2 h

/- English proof (translation)
The claim follows from `ENNReal.measurable_ofReal.comp (measurable_const.div ((Complex.measurable_im.comp measEmb.measurable).pow_const 2))`.
-/
theorem meas_rho : Measurable (fun z : P => rho (val z)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div ((Complex.measurable_im.comp measEmb.measurable).pow_const 2))

end UpperTheory.Esk.HalfPlaneMeasureLemmas

namespace UpperTheory.Esk

open HalfPlaneMeasureLemmas in
/- English proof (translation)
Establish `: LocallyCompactSpace P` using `openEmb.locallyCompactSpace`. Establish `: IsFiniteMeasureOnCompacts (Measure.comap val volume)` using `.comap' _ openEmb.continuous measEmb`. Establish `: SigmaFinite (Measure.comap val volume)` using `inferInstance`. Use `⟨?_, ?_, fun g => ⟨cont g, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[vol_def]`.

Conclude with `SigmaFinite.withDensity_ofReal _`. Establish `: (Measure.comap val volume).IsOpenPosMeasure` using `Measure.IsOpenPosMeasure.comap _ openEmb`. Use `⟨fun A hA hne => ?_⟩` and prove the remaining obligations. Rewrite using `[vol_def, Ne, withDensity_apply_eq_zero meas_rho]`. Establish `: {x : P | rho (val x) ≠ 0} ∩ A = A`.

Use `Set.inter_eq_right.2 (fun x _ => ?_)` and prove the remaining obligations. Use `x.2` as an intermediate fact. Simplify using `only [Set.mem_ofPred_eq, rho, val, ne_eq, ENNReal.ofReal_eq_zero, not_le]`. Check the signs of the components of the expression. Rewrite using `[this]`.

Conclude with `hA.measure_ne_zero _ hne`. Use `⟨(cont g).measurable, Measure.ext fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply (cont g).measurable hs, vol_eq _ ((cont g).measurable hs), vol_eq _ hs, image_pre, key _ (measEmb.measurableSet_image.2 hs)]`. Introduce and unpack `_ ⟨p, -, rfl⟩`. Conclude with `p.2`.
-/
theorem half_plane_measure_invariant_proof : B1a := by
  have : LocallyCompactSpace P := openEmb.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts (Measure.comap val volume) := .comap' _ openEmb.continuous measEmb
  have : SigmaFinite (Measure.comap val volume) := inferInstance
  refine ⟨?_, ?_, fun g => ⟨cont g, ?_⟩⟩
  · rw [vol_def]
    exact SigmaFinite.withDensity_ofReal _
  · have : (Measure.comap val volume).IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ openEmb
    refine ⟨fun A hA hne => ?_⟩
    rw [vol_def, Ne, withDensity_apply_eq_zero meas_rho]
    have : {x : P | rho (val x) ≠ 0} ∩ A = A := by
      refine Set.inter_eq_right.2 (fun x _ => ?_)
      have := x.2
      simp only [Set.mem_ofPred_eq, rho, val, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [this]
    exact hA.measure_ne_zero _ hne
  · refine ⟨(cont g).measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply (cont g).measurable hs, vol_eq _ ((cont g).measurable hs), vol_eq _ hs,
      image_pre, key _ (measEmb.measurableSet_image.2 hs)]
    rintro _ ⟨p, -, rfl⟩
    exact p.2

end UpperTheory.Esk
