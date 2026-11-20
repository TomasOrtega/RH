import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Introduce `k R _ _ _ _ A _ _ n b c hc g hg`. Use `haveI : Module.Finite k A := Module.Finite.of_basis b`. Set `e : A ⊗[k] R ≃ₐ[k] R ⊗[k] A` to `Algebra.TensorProduct.comm k A R`. Set `τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R` to `Algebra.TensorProduct.congr AlgEquiv.refl c`. Establish `hτ : UpperTheory.ConvolutionTheory.D.IsGal τ 2` using `(UpperTheory.ConvolutionTheory.D.galBase k R A c 2 hc).2.2.2`.

Establish `he : ∀ z, e (τ z) = UpperTheory.ConvolutionTheory.D.io c A (e z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a r => simp [e, τ, UpperTheory.ConvolutionTheory.D.io]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `h1 : ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) * UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1`. Establish `h2 : UpperTheory.ConvolutionTheory.D.io c A (g : R ⊗[k] A) * UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `h2`, the goal using `[Units.inv_eq_of_mul_eq_one_right hg.1]`.

Conclude with `h2`. Set `a : (A ⊗[k] R)ˣ` to `Units.map (e.symm : R ⊗[k] A →* A ⊗[k] R) g⁻¹`. Establish `ha : e (a : A ⊗[k] R) = ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A)` using `e.apply_symm_apply _`. Take `⟨z, hz⟩` from `UpperTheory.ConvolutionTheory.D.h90 k k A (A ⊗[k] R) τ 2 hτ a (by`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one, AlgEquiv.one_apply, map_mul, he, ha, h1, map_one])`. Use `⟨Units.map (e : A ⊗[k] R →* R ⊗[k] A) z, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg e hz`. Rewrite `h3` using `[map_mul, he, ha]`. Express the relevant statement in the definitionally equal form `UpperTheory.ConvolutionTheory.D.io c A (e z) = g * e z`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.mul_inv_cancel_left]`. Use `_ = g * e z := by rw [h3]`.
-/
theorem UpperTheory.ConvolutionTheory.D.tBase :
    UpperTheory.ConvolutionTheory.D.TBase := by
  intro k R _ _ _ _ A _ _ n b c hc g hg
  haveI : Module.Finite k A := Module.Finite.of_basis b
  let e : A ⊗[k] R ≃ₐ[k] R ⊗[k] A := Algebra.TensorProduct.comm k A R
  let τ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R := Algebra.TensorProduct.congr AlgEquiv.refl c
  have hτ : UpperTheory.ConvolutionTheory.D.IsGal τ 2 := (UpperTheory.ConvolutionTheory.D.galBase k R A c 2 hc).2.2.2
  have he : ∀ z, e (τ z) = UpperTheory.ConvolutionTheory.D.io c A (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [e, τ, UpperTheory.ConvolutionTheory.D.io]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 : ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) *
      UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
    have h2 : UpperTheory.ConvolutionTheory.D.io c A (g : R ⊗[k] A) *
        UpperTheory.ConvolutionTheory.D.io c A ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [Units.inv_eq_of_mul_eq_one_right hg.1] at h2 ⊢
    exact h2
  let a : (A ⊗[k] R)ˣ := Units.map (e.symm : R ⊗[k] A →* A ⊗[k] R) g⁻¹
  have ha : e (a : A ⊗[k] R) = ((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) := e.apply_symm_apply _
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 k k A (A ⊗[k] R) τ 2 hτ a (by
    apply e.injective
    rw [Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one, AlgEquiv.one_apply,
      map_mul, he, ha, h1, map_one])
  refine ⟨Units.map (e : A ⊗[k] R →* R ⊗[k] A) z, ?_⟩
  have h3 := congrArg e hz
  rw [map_mul, he, ha] at h3
  change UpperTheory.ConvolutionTheory.D.io c A (e z) = g * e z
  calc UpperTheory.ConvolutionTheory.D.io c A (e z)
      = g * (((g⁻¹ : (R ⊗[k] A)ˣ) : R ⊗[k] A) * UpperTheory.ConvolutionTheory.D.io c A (e z)) := by
        rw [Units.mul_inv_cancel_left]
    _ = g * e z := by rw [h3]
