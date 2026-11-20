import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem cvb_int {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) (x : G) :
    Integrable (fun y => a y * b (y⁻¹ * x)) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (ha'.mul_right)

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. A detailed English derivation is pending.
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
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Assume the negation of the conclusion and derive a contradiction.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
private theorem cvb_cs {a b : G → ℂ} (ha' : HasCompactSupport a) (hb' : HasCompactSupport b) :
    HasCompactSupport (cv μ a b) := by
  refine HasCompactSupport.intro (K := tsupport a * tsupport b) (IsCompact.mul ha' hb') fun x hx => ?_
  by_contra h
  obtain ⟨y, z, hy, hz, rfl⟩ := cvb_supp μ x h
  exact hx (Set.mul_mem_mul (subset_tsupport _ hy) (subset_tsupport _ hz))

open scoped Pointwise in
/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
