import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.GM.convSpec :
    ConvSpec := by
  intro K _ _ n _ ν _ β γ
  obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _) continuous_id ν ν β γ
  have hex : ∃ δ : TI K n, ∀ x, δ x = ∫ y, β y * γ (y⁻¹ * x) ∂ν := ⟨g, hg⟩
  have h1 : ∀ x, GM.conv ν β γ x = ∫ y, β y * γ (y⁻¹ * x) ∂ν := by
    intro x
    unfold GM.conv
    rw [dif_pos hex]
    exact hex.choose_spec x
  refine ⟨h1, fun μ _ => ?_⟩
  have h2 : GM.conv ν β γ = g := by
    ext x
    exact (h1 x).trans (hg x).symm
  rw [h2]
  exact hop (LL μ) ((rightRegularRep (rationalGLOne K n) μ).compHom (archP K n) continuous_archP)
