import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermConvolutionArch
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousConstantTerm
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `K _ _ n r φ hφ`. Set `μ : Measure (archGroup K n)` to `Measure.haar`. Take `⟨d, b, ε, B, h1, h2, h3, h4, h5⟩` from `exists_archCartanData K n`. Take `⟨P, hPm, hPd, hP⟩` from `hφ.isSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero b ε B h1 h2 h3 h4 h5`. Take `⟨κ, hκs, hκc, -, hκ⟩` from `(isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd (U := Set.univ) Filter.univ_mem`.

Establish `hκcont : Continuous κ` using `IsExpLieAlgebra.IsTestFunction.continuous (isExpLieAlgebra K n) ⟨hκs, hκc⟩`. Establish `rep : ∀ g y, archSlice φ.1 g y = ∫ z, archSlice φ.1 g (y * z) * κ z ∂μ` using `fun g y => hκ _ (hP g) y`. Establish `repφ : ∀ g, φ.1 g = ∫ z, φ.1 (g * infEmb K n z) * κ z ∂μ`. Introduce `g`. Use `rep g 1` as an intermediate fact.

Simplify `this` using `[archSlice_apply]`. Establish `hc : Continuous φ.1` using `hφ.continuous`. Establish `hct` using `UpperTheory.constantTerm_convolution_arch K n r μ φ.1 φ.1 κ hc hκcont hκc repφ`. Establish `hctc` using `UpperTheory.continuous_constantTerm K n r φ.1 hc`. Establish `hsliceC : ∀ g, Continuous (archSlice (constantTerm r φ.1) g)`.

Introduce `g`. Use `show Continuous fun x => constantTerm r φ.1 (g * infEmb K n x)`. Conclude with `hctc.comp (continuous_const.mul continuous_infEmb)`. Establish `repct : ∀ g y, archSlice (constantTerm r φ.1) g y = ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ`. Introduce `g y`.

Simplify using `only [archSlice_apply]`. Rewrite using `[hct (g * infEmb K n y)]`. Simplify using `[mul_assoc, map_mul]`. Establish `hs : IsArchSmooth (constantTerm r φ.1)`. Introduce `g`.

Establish `hfun : archSlice (constantTerm r φ.1) g = fun y => ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ` using `funext (repct g)`. Rewrite using `[hfun]`. Conclude with `(isExpLieAlgebra K n).isSmoothFun_integral_mul μ (hsliceC g) ⟨hκs, hκc⟩`. Use `⟨hs, fun X => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Establish `hD` using `(isExpLieAlgebra K n).continuous_convDeriv hκs ((isExpLieAlgebra K n).ofLie X)`. Establish `hDc` using `(isExpLieAlgebra K n).hasCompactSupport_convDeriv hκc ((isExpLieAlgebra K n).ofLie X)`. Establish `repU : ∀ h, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 h = ∫ y, φ.1 (h * infEmb K n y) * (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ`. Introduce `h`. Rewrite using `[uAction_ι_apply, IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (φ.2 h) (rep h)]`.

Simplify using `[archSlice_apply]`. Rewrite using `[uAction_ι_apply, IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hs g) (repct g), UpperTheory.constantTerm_convolution_arch K n r μ φ.1 _ _ hc hD hDc repU g]`. Simplify using `[archSlice_apply]`.
-/
theorem UpperTheory.constantTerm_archSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : archSmooth K n), IsAutomorphicForm φ.1 → ∃ hs : IsArchSmooth (constantTerm r φ.1), ∀ X : (isExpLieAlgebra K n).lieSubalgebra, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨constantTerm r φ.1, hs⟩).1 = constantTerm r (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 := by
  intro K _ _ n r φ hφ
  let μ : Measure (archGroup K n) := Measure.haar
  obtain ⟨d, b, ε, B, h1, h2, h3, h4, h5⟩ := exists_archCartanData K n
  obtain ⟨P, hPm, hPd, hP⟩ :=
    hφ.isSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero b ε B h1 h2 h3 h4 h5
  obtain ⟨κ, hκs, hκc, -, hκ⟩ :=
    (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd
      (U := Set.univ) Filter.univ_mem
  have hκcont : Continuous κ :=
    IsExpLieAlgebra.IsTestFunction.continuous (isExpLieAlgebra K n) ⟨hκs, hκc⟩
  have rep : ∀ g y, archSlice φ.1 g y = ∫ z, archSlice φ.1 g (y * z) * κ z ∂μ :=
    fun g y => hκ _ (hP g) y
  have repφ : ∀ g, φ.1 g = ∫ z, φ.1 (g * infEmb K n z) * κ z ∂μ := by
    intro g
    have := rep g 1
    simpa [archSlice_apply] using this
  have hc : Continuous φ.1 := hφ.continuous
  have hct := UpperTheory.constantTerm_convolution_arch K n r μ φ.1 φ.1 κ hc hκcont hκc repφ
  have hctc := UpperTheory.continuous_constantTerm K n r φ.1 hc
  have hsliceC : ∀ g, Continuous (archSlice (constantTerm r φ.1) g) := by
    intro g
    show Continuous fun x => constantTerm r φ.1 (g * infEmb K n x)
    exact hctc.comp (continuous_const.mul continuous_infEmb)
  have repct : ∀ g y, archSlice (constantTerm r φ.1) g y
      = ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := by
    intro g y
    simp only [archSlice_apply]
    rw [hct (g * infEmb K n y)]
    simp [mul_assoc, map_mul]
  have hs : IsArchSmooth (constantTerm r φ.1) := by
    intro g
    have hfun : archSlice (constantTerm r φ.1) g
        = fun y => ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := funext (repct g)
    rw [hfun]
    exact (isExpLieAlgebra K n).isSmoothFun_integral_mul μ (hsliceC g) ⟨hκs, hκc⟩
  refine ⟨hs, fun X => ?_⟩
  funext g
  have hD := (isExpLieAlgebra K n).continuous_convDeriv hκs ((isExpLieAlgebra K n).ofLie X)
  have hDc := (isExpLieAlgebra K n).hasCompactSupport_convDeriv hκc ((isExpLieAlgebra K n).ofLie X)
  have repU : ∀ h, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 h
      = ∫ y, φ.1 (h * infEmb K n y)
          * (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
    intro h
    rw [uAction_ι_apply,
      IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (φ.2 h) (rep h)]
    simp [archSlice_apply]
  rw [uAction_ι_apply,
    IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hs g) (repct g),
    UpperTheory.constantTerm_convolution_arch K n r μ φ.1 _ _ hc hD hDc repU g]
  simp [archSlice_apply]
