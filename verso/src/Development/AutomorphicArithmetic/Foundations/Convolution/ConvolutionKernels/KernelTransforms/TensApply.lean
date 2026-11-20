import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensCont

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Establish `hc : Continuous fun s : {r : ℝ // 0 < r} => β (a * zInf K n s)` using `β.continuous.comp (continuous_const.mul continuous_zInf)`. Use `hc.integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Establish `hD : IsCompact ((fun r : {r : ℝ // 0 < r} => r * (detA K n a)⁻¹) '' (detA K n '' tsupport β))` using `(β.hasCompactSupport.isCompact.image continuous_detA).image (continuous_id.mul continuous_const)`. Use `HasCompactSupport.intro hD fun s hs => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Conclude with `hs ⟨s * detA K n a, mem_of_kernel_ne_zero hn hne, by simp⟩`.
-/
private theorem integrable_slice {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (a : archGroup K n) :
    Integrable (fun s => β (a * zInf K n s)) GroundTheory.Global.posRealMeasure := by
  have hc : Continuous fun s : {r : ℝ // 0 < r} => β (a * zInf K n s) :=
    β.continuous.comp (continuous_const.mul continuous_zInf)
  refine hc.integrable_of_hasCompactSupport ?_
  have hD : IsCompact ((fun r : {r : ℝ // 0 < r} => r * (detA K n a)⁻¹) '' (detA K n '' tsupport β)) :=
    (β.hasCompactSupport.isCompact.image continuous_detA).image (continuous_id.mul continuous_const)
  refine HasCompactSupport.intro hD fun s hs => ?_
  by_contra hne
  exact hs ⟨s * detA K n a, mem_of_kernel_ne_zero hn hne, by simp⟩

/- English proof (translation)
Simplify using `only [kbar, CompactlySupportedContinuousMap.add_apply]`. Conclude with `integral_add (integrable_slice hn β a) (integrable_slice hn β' a)`.
-/
private theorem kbar_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β β' : TI K n) (a : archGroup K n) : kbar (β + β' : TI K n) a = kbar β a + kbar β' a := by
  simp only [kbar, CompactlySupportedContinuousMap.add_apply]
  exact integral_add (integrable_slice hn β a) (integrable_slice hn β' a)

/- English proof (translation)
Simplify using `only [kbar, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]`. Conclude with `integral_const_mul c _`.
-/
private theorem kbar_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : ℂ) (β : TI K n) (a : archGroup K n) : kbar (c • β : TI K n) a = c * kbar β a := by
  simp only [kbar, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `UpperTheory.ConvolutionTheory.Tf.tensCont K n hn β e`. Establish `h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e)` using `⟨h1, h2⟩`. Rewrite using `[tens, dif_pos h]`. Both sides reduce to the same expression.
-/
private theorem tens_apply' {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (e : TF K n) (x : normOneGL K n) : tens β e x = tensFun β e x := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.tensCont K n hn β e
  have h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) := ⟨h1, h2⟩
  rw [tens, dif_pos h]
  rfl

/- English proof (translation)
Introduce `K _ _ n hn β e`. Use `⟨tens_apply' hn β e, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hC : IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e)` using `(β.hasCompactSupport.isCompact.image continuous_archP).mul (e.hasCompactSupport.isCompact.image MultiplicityOne.continuous_finProj)`. Use `closure_minimal ?_ hC.isClosed` and prove the remaining obligations. Introduce `x hx`.

Establish `hx' : tensFun β e x ≠ 0`. Rewrite using `[← tens_apply' hn β e x]`. Conclude with `hx`. Take `⟨a, ha, h, hh, rfl⟩` from `(UpperTheory.ConvolutionTheory.Tf.tensCont K n hn β e).2.2 x hx'`. Conclude with `Set.mul_mem_mul ⟨a, ha, rfl⟩ ⟨h, hh, rfl⟩`.

Introduce `β'`. Use extensionality with `x`. Simplify using `only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, kbar_add hn, add_mul]`. Introduce `e'`. Use extensionality with `x`.

Simplify using `only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, mul_add]`. Introduce `c`. Prove the components needed by the constructor for the conclusion. Use extensionality with `x`. Simplify using `only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, kbar_smul, smul_eq_mul, mul_assoc]`.

Use extensionality with `x`. Simplify using `only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.Tf.tensApply :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n), (∀ x, tens β e x = tensFun β e x) ∧
      (tsupport (tens β e) ⊆ archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      (∀ β', tens (β + β') e = tens β e + tens β' e) ∧ (∀ e', tens β (e + e') = tens β e + tens β e') ∧
      ∀ c : ℂ, tens (c • β) e = c • tens β e ∧ tens β (c • e) = c • tens β e := by
  intro K _ _ n hn β e
  refine ⟨tens_apply' hn β e, ?_, ?_, ?_, ?_⟩
  · have hC : IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) :=
      (β.hasCompactSupport.isCompact.image continuous_archP).mul
        (e.hasCompactSupport.isCompact.image MultiplicityOne.continuous_finProj)
    refine closure_minimal ?_ hC.isClosed
    intro x hx
    have hx' : tensFun β e x ≠ 0 := by
      rw [← tens_apply' hn β e x]
      exact hx
    obtain ⟨a, ha, h, hh, rfl⟩ := (UpperTheory.ConvolutionTheory.Tf.tensCont K n hn β e).2.2 x hx'
    exact Set.mul_mem_mul ⟨a, ha, rfl⟩ ⟨h, hh, rfl⟩
  · intro β'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, kbar_add hn, add_mul]
  · intro e'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, mul_add]
  · intro c
    constructor
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, kbar_smul,
        smul_eq_mul, mul_assoc]
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, smul_eq_mul]
      ring
