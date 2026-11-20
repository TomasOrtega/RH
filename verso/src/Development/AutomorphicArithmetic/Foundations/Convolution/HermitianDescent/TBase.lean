import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
