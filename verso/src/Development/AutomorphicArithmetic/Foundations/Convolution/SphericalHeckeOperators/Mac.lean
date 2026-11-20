import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoVol
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation.
-/
theorem UpperTheory.ConvolutionTheory.H.mac :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (z : Fin n → ℂˣ) (a : Fin n → ℤ), Antitone a →
      vPoly n ((qF F : ℂ))⁻¹ * ∫ g, th μ a g * zonalSpherical μ z g ∂μ = evalAt z (hlR ((qF F : ℂ))⁻¹ a) := by
  intro F _ _ _ _ n _ _ μ _ z a ha
  have hm : MeasurableSet (dco F a) := by
    have h := ((dcoShape F n a ha).2.2.1.1.isOpen_fiber 1).measurableSet
    convert h using 1
    ext g
    by_cases hg : g ∈ dco F a <;> simp [uFn, hg]
  have hI : (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_iwahori F n) (isOpen_iwahori F n)).ne'
  have e : (fun g => th μ a g * zonalSpherical μ z g) = (dco F a).indicator fun _ =>
      halfModulus F a / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) * zonalSpherical μ z (torusPow F n a) := by
    funext g
    by_cases hg : g ∈ dco F a
    · rw [Set.indicator_of_mem hg, th, Pi.smul_apply, uFn, Set.indicator_of_mem hg]
      obtain ⟨x, hx, y, hy, rfl⟩ := hg
      rw [zonalSpherical_mul_right z _ (iwahori_le_integralGL F n hy),
        zonalSpherical_mul_left z (iwahori_le_integralGL F n hx)]
      simp
    · simp [th, uFn, hg]
  rw [e, integral_indicator_const _ hm, Complex.real_smul]
  have h1 := macdonald_formula_hlR (μ := μ) z ha
  have h2 := dcoVol F n μ a ha
  apply mul_right_cancel₀ hI
  calc _ = (μ.real (dco F a) : ℂ) * halfModulus F a *
        (vPoly n ((qF F : ℂ))⁻¹ * zonalSpherical μ z (torusPow F n a)) := by field_simp
    _ = _ := by rw [h1, ← h2]; ring
