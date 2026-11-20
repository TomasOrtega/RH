import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
/- English proof (translation)
The claim follows from `Continuous.integrable_of_hasCompactSupport (by fun_prop) (ha'.mul_right)`.
-/
private theorem cvb_int {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) (x : G) :
    Integrable (fun y => a y * b (y⁻¹ * x)) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (ha'.mul_right)

/- English proof (translation)
Establish `h : cv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ`. Use function extensionality and compare the values at `x`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm` and prove the remaining obligations. Rewrite using `[image_eq_zero_of_notMem_tsupport hy, zero_mul]`. Rewrite using `[h]`.

Use `continuous_parametric_integral_of_continuous (f := fun x y => a y * b (y⁻¹ * x)) ?_ ha'` and prove the remaining obligations. Unfold `Function.uncurry`. Use `fun_prop`.
-/
private theorem cvb_cont {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) :
    Continuous (cv μ a b) := by
  have h : cv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [h]
  refine continuous_parametric_integral_of_continuous (f := fun x y => a y * b (y⁻¹ * x)) ?_ ha'
  unfold Function.uncurry
  fun_prop

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Apply `hx` to reduce the goal to its premises. Establish `: (fun y => a y * b (y⁻¹ * x)) = fun _ => 0`. Use function extensionality and compare the values at `y`. Assume the negation of the conclusion as `h'`.

Conclude with `h ⟨y, y⁻¹ * x, left_ne_zero_of_mul h', right_ne_zero_of_mul h', by simp⟩`. Simplify using `only [cv, this, integral_zero]`.
-/
private theorem cvb_supp {a b : G → ℂ} (x : G) (hx : cv μ a b x ≠ 0) :
    ∃ y z, a y ≠ 0 ∧ b z ≠ 0 ∧ x = y * z := by
  by_contra h
  apply hx
  have : (fun y => a y * b (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_contra h'
    exact h ⟨y, y⁻¹ * x, left_ne_zero_of_mul h', right_ne_zero_of_mul h', by simp⟩
  simp only [cv, this, integral_zero]

open scoped Pointwise in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
/- English proof (translation)
Use `HasCompactSupport.intro (K := tsupport a * tsupport b) (IsCompact.mul ha' hb') fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Take `⟨y, z, hy, hz, rfl⟩` from `cvb_supp μ x h`. Conclude with `hx (Set.mul_mem_mul (subset_tsupport _ hy) (subset_tsupport _ hz))`.
-/
private theorem cvb_cs {a b : G → ℂ} (ha' : HasCompactSupport a) (hb' : HasCompactSupport b) :
    HasCompactSupport (cv μ a b) := by
  refine HasCompactSupport.intro (K := tsupport a * tsupport b) (IsCompact.mul ha' hb') fun x hx => ?_
  by_contra h
  obtain ⟨y, z, hy, hz, rfl⟩ := cvb_supp μ x h
  exact hx (Set.mul_mem_mul (subset_tsupport _ hy) (subset_tsupport _ hz))

open scoped Pointwise in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hint : Integrable (Function.uncurry fun y z : G => a z * b (z⁻¹ * y) * c (y⁻¹ * x)) (μ.prod μ)`. Use `Continuous.integrable_of_hasCompactSupport ?_ ?_` and prove the remaining obligations. Unfold `Function.uncurry fun_prop`. Use `HasCompactSupport.intro (K := (tsupport a * tsupport b) ×ˢ tsupport a) ((IsCompact.mul ha' hb').prod ha') fun p hp => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Establish `h1` using `left_ne_zero_of_mul h`. Establish `h2 : a p.2 ≠ 0` using `left_ne_zero_of_mul h1`. Establish `h3 : b (p.2⁻¹ * p.1) ≠ 0` using `right_ne_zero_of_mul h1`. Use `hp ⟨?_, subset_tsupport _ h2⟩` and prove the remaining obligations.

Use `Set.mul_mem_mul (subset_tsupport _ h2) (subset_tsupport _ h3)` as an intermediate fact. Simplify using `using this`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [cv, integral_mul_const]`. Use `_ = ∫ z, ∫ y, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := integral_integral_swap hint`.

Use `_ = cv μ a (cv μ b c) x := by`. Simplify using `only [cv]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← integral_const_mul, ← integral_mul_left_eq_self _ z]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
private theorem cvb_assoc {a b c : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b)
    (hb' : HasCompactSupport b) (hc : Continuous c) : cv μ (cv μ a b) c = cv μ a (cv μ b c) := by
  funext x
  have hint : Integrable (Function.uncurry fun y z : G => a z * b (z⁻¹ * y) * c (y⁻¹ * x)) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold Function.uncurry
      fun_prop
    · refine HasCompactSupport.intro (K := (tsupport a * tsupport b) ×ˢ tsupport a)
        ((IsCompact.mul ha' hb').prod ha') fun p hp => ?_
      by_contra h
      have h1 := left_ne_zero_of_mul h
      have h2 : a p.2 ≠ 0 := left_ne_zero_of_mul h1
      have h3 : b (p.2⁻¹ * p.1) ≠ 0 := right_ne_zero_of_mul h1
      refine hp ⟨?_, subset_tsupport _ h2⟩
      have := Set.mul_mem_mul (subset_tsupport _ h2) (subset_tsupport _ h3)
      simpa using this
  calc cv μ (cv μ a b) c x = ∫ y, ∫ z, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := by
        simp only [cv, integral_mul_const]
    _ = ∫ z, ∫ y, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := integral_integral_swap hint
    _ = cv μ a (cv μ b c) x := by
        simp only [cv]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_const_mul, ← integral_mul_left_eq_self _ z]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [mul_assoc]

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ a b c ha ha' hb hb' hc hc'`. Use `⟨cvb_cont μ ha ha' hb, cvb_cs μ ha' hb', cvb_supp μ, cvb_assoc μ ha ha' hb hb' hc, ?_, ?_, fun t => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [cv, Pi.add_apply, add_mul]`. Conclude with `integral_add (cvb_int μ ha ha' hc x) (cvb_int μ hb hb' hc x)`.

Use function extensionality and compare the values at `x`. Simplify using `only [cv, Pi.add_apply, mul_add]`. Conclude with `integral_add (cvb_int μ ha ha' hb x) (cvb_int μ ha ha' hc x)`. Use function extensionality and compare the values at `x`. Simplify using `only [cv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]`.

Use function extensionality and compare the values at `x`. Simplify using `only [cv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ t, integral_const_mul]`.
-/
theorem UpperTheory.ConvolutionTheory.L1.cvBasic :
    UpperTheory.ConvolutionTheory.L1.CvBasic := by
  intro G _ _ _ _ _ _ _ _ μ _ a b c ha ha' hb hb' hc hc'
  refine ⟨cvb_cont μ ha ha' hb, cvb_cs μ ha' hb', cvb_supp μ, cvb_assoc μ ha ha' hb hb' hc, ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · funext x
    simp only [cv, Pi.add_apply, add_mul]
    exact integral_add (cvb_int μ ha ha' hc x) (cvb_int μ hb hb' hc x)
  · funext x
    simp only [cv, Pi.add_apply, mul_add]
    exact integral_add (cvb_int μ ha ha' hb x) (cvb_int μ ha ha' hc x)
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ t, integral_const_mul]
