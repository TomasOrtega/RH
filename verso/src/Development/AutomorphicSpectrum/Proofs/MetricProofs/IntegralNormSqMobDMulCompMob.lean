import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

/- English proof (translation)
Introduce `a ha b hb`. Establish `ha' : p + q * a = 0` using `ha`. Establish `hb' : p + q * b = 0` using `hb`. Establish `hq : q ≠ 0`. Break down `h with hp | hq` into its components or cases.

Introduce `hq0`. Rewrite `ha'` using `[hq0, zero_mul, add_zero]`. Conclude with `hp ha'`. Conclude with `hq`. Conclude with `mul_left_cancel₀ hq (by linear_combination ha' - hb')`.
-/
theorem subsingleton_affine_zero {p q : ℂ} (h : p ≠ 0 ∨ q ≠ 0) :
    {a : ℂ | p + q * a = 0}.Subsingleton := by
  intro a ha b hb
  have ha' : p + q * a = 0 := ha
  have hb' : p + q * b = 0 := hb
  have hq : q ≠ 0 := by
    rcases h with hp | hq
    · intro hq0
      rw [hq0, zero_mul, add_zero] at ha'
      exact hp ha'
    · exact hq
  exact mul_left_cancel₀ hq (by linear_combination ha' - hb')

/- English proof (translation)
Establish `e : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w = w • ContinuousLinearMap.id ℂ ℂ`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[e, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, ReciprocityTheory.AnForm.A.det_restrictScalars_real]`. Simplify using the standard rewrite rules.
-/
theorem det_smulRight_restrictScalars (w : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ).det = Complex.normSq w := by
  have e : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w = w • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  rw [e, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    ReciprocityTheory.AnForm.A.det_restrictScalars_real]
  simp

/- English proof (translation)
Unfold `mob mobD`. Unfold `den at *`. Establish `h1 : HasDerivAt (fun a => g 1 0 + g 1 1 * a) (g 1 1) a`. Simplify using `using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)`. Establish `h2 : HasDerivAt (fun a => g 0 0 + g 0 1 * a) (g 0 1) a`.

Simplify using `using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)`. Use `(h1.div h2 ha).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[det_fin_two]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_mob (g : Matrix (Fin 2) (Fin 2) ℂ) {a : ℂ} (ha : den g a ≠ 0) :
    HasDerivAt (mob g) (mobD g a) a := by
  unfold mob mobD
  unfold den at *
  have h1 : HasDerivAt (fun a => g 1 0 + g 1 1 * a) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun a => g 0 0 + g 0 1 * a) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  refine (h1.div h2 ha).congr_deriv ?_
  rw [det_fin_two]
  congr 1
  ring

/- English proof (translation)
Introduce `a ha b hb hab`. Establish `ha' : den g a ≠ 0` using `ha`. Establish `hb' : den g b ≠ 0` using `hb`. Unfold `mob at hab`. Rewrite `hab` using `[div_eq_div_iff ha' hb']`.

Unfold `den at hab`. Rewrite `hg` using `[det_fin_two]`. Establish `h : (a - b) * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 0` using `by linear_combination hab`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`.

Conclude with `absurd h hg`.
-/
theorem injOn_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) :
    Set.InjOn (mob g) {a | den g a ≠ 0} := by
  intro a ha b hb hab
  have ha' : den g a ≠ 0 := ha
  have hb' : den g b ≠ 0 := hb
  unfold mob at hab
  rw [div_eq_div_iff ha' hb'] at hab
  unfold den at hab
  rw [det_fin_two] at hg
  have h : (a - b) * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 0 := by linear_combination hab
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hg

/- English proof (translation)
Establish `hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0` using `by rwa [det_fin_two] at hg`. Establish `hci : (g 1 1 + -g 0 1 * b) * (g 1 1 + -g 0 1 * b)⁻¹ = 1` using `mul_inv_cancel₀ hb`. Establish `hden : den g ((g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b)) = (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (g 1 1 + (-g 0 1) * b)⁻¹`. Unfold `den`. Rewrite using `[div_eq_mul_inv]`.

Take the linear combination `(-g 0 0) * hci`. Use `⟨(g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b), ?_, ?_⟩` and prove the remaining obligations. Use `show den g _ ≠ 0`. Rewrite using `[hden]`. Conclude with `mul_ne_zero hd (inv_ne_zero hb)`.

Unfold `mob`. Rewrite using `[hden, div_eq_iff (mul_ne_zero hd (inv_ne_zero hb)), div_eq_mul_inv (g 0 0 * b - g 1 0)]`. Take the linear combination `(-g 1 0) * hci`.
-/
theorem mem_image_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) {b : ℂ}
    (hb : g 1 1 + (-g 0 1) * b ≠ 0) : b ∈ mob g '' {a | den g a ≠ 0} := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [det_fin_two] at hg
  have hci : (g 1 1 + -g 0 1 * b) * (g 1 1 + -g 0 1 * b)⁻¹ = 1 := mul_inv_cancel₀ hb
  have hden : den g ((g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b)) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (g 1 1 + (-g 0 1) * b)⁻¹ := by
    unfold den
    rw [div_eq_mul_inv]
    linear_combination (-g 0 0) * hci
  refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b), ?_, ?_⟩
  · show den g _ ≠ 0
    rw [hden]
    exact mul_ne_zero hd (inv_ne_zero hb)
  · unfold mob
    rw [hden, div_eq_iff (mul_ne_zero hd (inv_ne_zero hb)), div_eq_mul_inv (g 0 0 * b - g 1 0)]
    linear_combination (-g 1 0) * hci

/- English proof (translation)
Establish `hdet : g.det ≠ 0` using `hu.ne_zero`. Establish `hcont : Continuous (den g)`. Unfold `den`. Use `fun_prop`. Establish `hs : MeasurableSet {a : ℂ | den g a ≠ 0}` using `(isOpen_ne_fun hcont continuous_const).measurableSet`.

Establish `hderiv : ∀ a ∈ {a : ℂ | den g a ≠ 0}, HasFDerivWithinAt (mob g) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (mobD g a)).restrictScalars ℝ) {a : ℂ | den g a ≠ 0} a` using `fun a ha => ((hasDerivAt_mob g ha).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`. Establish `hcv` using `integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv (injOn_mob g hdet) f`. Simplify using `only [det_smulRight_restrictScalars, abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul] at hcv`. Rewrite `hdet` using `[det_fin_two]`. Establish `hnull1 : ∀ᵐ a ∂(volume : Measure ℂ), a ∈ {a : ℂ | den g a ≠ 0}`.

Establish `h01 : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_or, not_not, not_not]`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[hc.1, hc.2]`.

Expand and normalize the polynomial expressions, which then agree. Use `mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h01).countable.measure_zero _))` and prove the remaining obligations. Introduce `a ha`. Establish `ha' : ¬ den g a ≠ 0` using `ha`. Rewrite `ha'` using `[not_not]`.

Conclude with `ha'`. Establish `hnull2 : ∀ᵐ b ∂(volume : Measure ℂ), b ∈ mob g '' {a : ℂ | den g a ≠ 0}`. Establish `h11 : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_or, not_not, not_not, neg_eq_zero]`.

Apply `hdet` to reduce the goal to its premises. Rewrite using `[hc.1, hc.2]`. Expand and normalize the polynomial expressions, which then agree. Use `mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h11).countable.measure_zero _))` and prove the remaining obligations. Introduce `b hb`.

Assume the negation of the conclusion as `hne`. Conclude with `hb (mem_image_mob g hu.ne_zero hne)`. Rewrite `hcv` using `[Measure.restrict_eq_self_of_ae_mem hnull1, Measure.restrict_eq_self_of_ae_mem hnull2]`. Conclude with `hcv.symm`.
-/
theorem integral_normSq_mobD_mul_comp_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit g.det)
    (f : ℂ → ℝ) :
    ∫ a : ℂ, Complex.normSq (mobD g a) * f (mob g a) = ∫ b : ℂ, f b := by
  have hdet : g.det ≠ 0 := hu.ne_zero
  have hcont : Continuous (den g) := by
    unfold den
    fun_prop
  have hs : MeasurableSet {a : ℂ | den g a ≠ 0} := (isOpen_ne_fun hcont continuous_const).measurableSet
  have hderiv : ∀ a ∈ {a : ℂ | den g a ≠ 0}, HasFDerivWithinAt (mob g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (mobD g a)).restrictScalars ℝ)
      {a : ℂ | den g a ≠ 0} a :=
    fun a ha => ((hasDerivAt_mob g ha).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv (injOn_mob g hdet) f
  simp only [det_smulRight_restrictScalars, abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul] at hcv
  rw [det_fin_two] at hdet
  have hnull1 : ∀ᵐ a ∂(volume : Measure ℂ), a ∈ {a : ℂ | den g a ≠ 0} := by
    have h01 : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h01).countable.measure_zero _))
    intro a ha
    have ha' : ¬ den g a ≠ 0 := ha
    rw [not_not] at ha'
    exact ha'
  have hnull2 : ∀ᵐ b ∂(volume : Measure ℂ), b ∈ mob g '' {a : ℂ | den g a ≠ 0} := by
    have h11 : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not, neg_eq_zero] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h11).countable.measure_zero _))
    intro b hb
    by_contra hne
    exact hb (mem_image_mob g hu.ne_zero hne)
  rw [Measure.restrict_eq_self_of_ae_mem hnull1, Measure.restrict_eq_self_of_ae_mem hnull2] at hcv
  exact hcv.symm

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
