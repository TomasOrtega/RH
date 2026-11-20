import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtCompact
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ConvSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped Pointwise

/- English proof (translation)
Introduce `K _ _ n hn ν _ a₀ ha₀`. Establish `hT : IsCompact (tsupport (a₀ : archGroup K n → ℂ))` using `a₀.hasCompactSupport`. Use `set S : Set (AdelicGLn.AdelicGL K n) := (infEmb K n) '' tsupport (a₀ : archGroup K n → ℂ) with hS`. Take `⟨Y, hY1, -, hY⟩` from `UpperTheory.ConvolutionTheory.Tf.htCompact K n S (hT.image AutomorphicForm.continuous_infEmb)`. Establish `hlet : ∀ (x : Option (Ix K n)) (y : archGroup K n), letter a₀ x y ≠ 0 → y ∈ tsupport (a₀ : archGroup K n → ℂ)`.

Introduce `x y hy`. Consider the cases of `x with`. Consider the case `none => exact subset_tsupport _ hy`. Consider the case `some x`. Take `⟨-, -, h2, -⟩` from `UpperTheory.ConvolutionTheory.Tf.lactSpec K n a₀ ha₀`.

Conclude with `(h2 (zc x.1 x.2)).2 (subset_tsupport _ hy)`. Establish `key : ∀ (wd : List (Option (Ix K n))) (g : archGroup K n), word ν a₀ wd g ≠ 0 → infEmb K n g ∈ S ^ (wd.length + 1)`. Introduce `wd`. Proceed by induction on `wd with`. Consider the case `nil`.

Introduce `g hg`. Establish `hg' : a₀ g ≠ 0` using `hg`. Rewrite using `[List.length_nil, zero_add, pow_one]`. Conclude with `Set.mem_image_of_mem _ (subset_tsupport _ hg')`. Consider the case `cons x w ih`.

Introduce `g hg`. Establish `hc : (∫ y, letter a₀ x y * word ν a₀ w (y⁻¹ * g) ∂ν) ≠ 0`. Use `(UpperTheory.ConvolutionTheory.GM.convSpec K n hn ν (letter a₀ x) (word ν a₀ w)).1 g` as an intermediate fact. Rewrite using `[← this]`. Conclude with `hg`.

Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, letter a₀ x y * word ν a₀ w (y⁻¹ * g) ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hc (by simp [hne])`. Establish `hy1` using `left_ne_zero_of_mul hy`.

Establish `hy2` using `right_ne_zero_of_mul hy`. Establish `hm` using `ih _ hy2`. Establish `he : infEmb K n g = infEmb K n y * infEmb K n (y⁻¹ * g)`. Rewrite using `[← map_mul, mul_inv_cancel_left]`. Rewrite using `[List.length_cons, pow_succ', he]`.

Conclude with `Set.mul_mem_mul (Set.mem_image_of_mem _ (hlet x y hy1)) hm`. Conclude with `⟨Y, hY1, fun wd g hg => hY _ _ (key wd g hg)⟩`.
-/
theorem UpperTheory.ConvolutionTheory.GM.wordHt :
    WordHt := by
  intro K _ _ n hn ν _ a₀ ha₀
  have hT : IsCompact (tsupport (a₀ : archGroup K n → ℂ)) := a₀.hasCompactSupport
  set S : Set (AdelicGLn.AdelicGL K n) := (infEmb K n) '' tsupport (a₀ : archGroup K n → ℂ) with hS
  obtain ⟨Y, hY1, -, hY⟩ := UpperTheory.ConvolutionTheory.Tf.htCompact K n S (hT.image AutomorphicForm.continuous_infEmb)
  have hlet : ∀ (x : Option (Ix K n)) (y : archGroup K n), letter a₀ x y ≠ 0 →
      y ∈ tsupport (a₀ : archGroup K n → ℂ) := by
    intro x y hy
    cases x with
    | none => exact subset_tsupport _ hy
    | some x =>
      obtain ⟨-, -, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n a₀ ha₀
      exact (h2 (zc x.1 x.2)).2 (subset_tsupport _ hy)
  have key : ∀ (wd : List (Option (Ix K n))) (g : archGroup K n), word ν a₀ wd g ≠ 0 →
      infEmb K n g ∈ S ^ (wd.length + 1) := by
    intro wd
    induction wd with
    | nil =>
      intro g hg
      have hg' : a₀ g ≠ 0 := hg
      rw [List.length_nil, zero_add, pow_one]
      exact Set.mem_image_of_mem _ (subset_tsupport _ hg')
    | cons x w ih =>
      intro g hg
      have hc : (∫ y, letter a₀ x y * word ν a₀ w (y⁻¹ * g) ∂ν) ≠ 0 := by
        have := (UpperTheory.ConvolutionTheory.GM.convSpec K n hn ν (letter a₀ x) (word ν a₀ w)).1 g
        rw [← this]
        exact hg
      obtain ⟨y, hy⟩ : ∃ y, letter a₀ x y * word ν a₀ w (y⁻¹ * g) ≠ 0 := by
        by_contra hne
        push_neg at hne
        exact hc (by simp [hne])
      have hy1 := left_ne_zero_of_mul hy
      have hy2 := right_ne_zero_of_mul hy
      have hm := ih _ hy2
      have he : infEmb K n g = infEmb K n y * infEmb K n (y⁻¹ * g) := by
        rw [← map_mul, mul_inv_cancel_left]
      rw [List.length_cons, pow_succ', he]
      exact Set.mul_mem_mul (Set.mem_image_of_mem _ (hlet x y hy1)) hm
  exact ⟨Y, hY1, fun wd g hg => hY _ _ (key wd g hg)⟩
