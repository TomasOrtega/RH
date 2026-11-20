import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

open MeasureTheory NumberField PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.K

open GroundTheory.Global.AdeleBaseChange in
open scoped NumberField.AdeleRing TensorProduct in
/- English proof (translation)
Use `adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l`. Rewrite using `[adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, GroundTheory.Global.AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F]) ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a`.

Rewrite using `[adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, smul_adeleMap, map_one, map_one, one_mul]`. Both sides reduce to the same expression.
-/
private theorem galAd_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
  refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
  · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
      ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
    rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
      GroundTheory.Global.AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
    rfl
  · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
      ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
    rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
      smul_adeleMap, map_one, map_one, one_mul]
    rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ`. Use `UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv (galAd σ) ?_ fun x => ?_` and prove the remaining obligations. Rewrite using `[galAd_eq_smul]`. Conclude with `continuous_const_smul σ`. Rewrite using `[galAd_eq_smul]`.

Conclude with `GroundTheory.Global.AdeleBaseChange.smul_algebraMap σ x`.
-/
theorem UpperTheory.ConvolutionTheory.K.galAdEq :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E),
      galAd σ = Formalism.L2.Host.CT.adMap σ.toRingEquiv := by
  intro F E _ _ _ _ _ σ
  refine UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv (galAd σ) ?_ fun x => ?_
  · rw [galAd_eq_smul]
    exact continuous_const_smul σ
  · rw [galAd_eq_smul]
    exact GroundTheory.Global.AdeleBaseChange.smul_algebraMap σ x
