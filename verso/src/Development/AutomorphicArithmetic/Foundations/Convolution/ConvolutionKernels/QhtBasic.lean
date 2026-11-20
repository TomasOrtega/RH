import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.Reduction
open IsDedekindDomain

namespace UpperTheory.ConvolutionTheory.K

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem continuous_locHeight {E : Type*} [NormedField E] {n : ℕ} :
    Continuous (locHeight : GL (Fin n) E → ℝ) := by
  unfold locHeight
  refine continuous_const.max (NNReal.continuous_coe.comp ?_)
  refine Continuous.finset_sup_apply fun p _ => ?_
  refine Continuous.max ?_ ?_
  · exact (continuous_GL_apply p.1 p.2).nnnorm
  · exact ((continuous_GL_apply p.1 p.2).comp continuous_inv).nnnorm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
private theorem locHeight_mul_integral {K : Type} [Field K] [NumberField K] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 K)} (x k : GL (Fin n) (v.adicCompletion K))
    (hk : k ∈ GLnLocal.integralGL (v.adicCompletion K) n) : locHeight (x * k) = locHeight x := by
  refine le_antisymm ?_ ?_
  · have h := locHeight_mul_le_of_ultrametric x k
    rwa [locHeight_eq_one_of_mem_integralGL hk, mul_one] at h
  · have h := locHeight_mul_le_of_ultrametric (x * k) k⁻¹
    rwa [locHeight_eq_one_of_mem_integralGL (inv_mem hk), mul_one, mul_inv_cancel_right] at h

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem finprod_mul_integral {K : Type} [Field K] [NumberField K] {n : ℕ}
    (g w : AdelicGLn.AdelicGL K n)
    (hw : (AdelicGLn.prodEquiv K n w).2 ∈ AdelicGLn.integralFiniteGL K n) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v (g * w)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff_forall] at hw
  refine finprod_congr fun v => ?_
  rw [finAt_mul]
  exact locHeight_mul_integral _ _ (hw v)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
private theorem continuous_finprod {K : Type} [Field K] [NumberField K] {n : ℕ} :
    Continuous fun g : AdelicGLn.AdelicGL K n =>
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  have hcF : Continuous fun g : AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n g).2 :=
    continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((fun g => (AdelicGLn.prodEquiv K n g).2) ⁻¹'
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))), ?_, ?_, ?_⟩
  · exact ((AdelicGLn.isOpen_integralFiniteGL K n).preimage hcF).preimage
      (continuous_const.mul continuous_id)
  · simp only [Set.mem_preimage, inv_mul_cancel, map_one, Prod.snd_one, SetLike.mem_coe]
    exact one_mem _
  · intro y hy
    have := finprod_mul_integral x (x⁻¹ * y) hy
    rwa [mul_inv_cancel_left] at this

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem continuous_height {K : Type} [Field K] [NumberField K] {n : ℕ} :
    Continuous (AutomorphicForm.height : AdelicGLn.AdelicGL K n → ℝ) := by
  unfold AutomorphicForm.height
  refine Continuous.mul ?_ continuous_finprod
  exact continuous_finset_prod _ fun w _ => (continuous_locHeight.comp (continuous_infAt w)).pow _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem measurable_qht {K : Type} [Field K] [NumberField K] {n : ℕ} :
    Measurable (qht : G1 K n → ℝ) := by
  haveI : Countable (Gam K n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  unfold qht
  refine Measurable.iInf fun γ => Continuous.measurable ?_
  exact continuous_height.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
private theorem qht_mul_left {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : G1 K n)
    (hγ : γ ∈ Gam K n) (x : G1 K n) : qht (γ * x) = qht x := by
  unfold qht
  have h := (Equiv.mulRight (⟨γ, hγ⟩ : Gam K n)).iInf_comp
    (g := fun δ : Gam K n => AutomorphicForm.height (((δ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n))
  rw [← h]
  refine congrArg _ (funext fun δ => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]

end UpperTheory.ConvolutionTheory.K

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.K.qhtBasic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ x : G1 K n, 1 ≤ qht x) ∧ (∀ γ ∈ Gam K n, ∀ x : G1 K n, qht (γ * x) = qht x) ∧
      Measurable fun y : RightCosetSpace (Gam K n) => qht (Quotient.out y : G1 K n) := by
  intro K _ _ n
  refine ⟨fun x => le_ciInf fun _ => one_le_height _, qht_mul_left, ?_⟩
  rw [measurable_from_quotient]
  have h : ((fun y : RightCosetSpace (Gam K n) => qht (Quotient.out y : G1 K n)) ∘ Quotient.mk'') =
      (qht : G1 K n → ℝ) := by
    funext x
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (mk (Gam K n) x))
    change qht (Quotient.out (mk (Gam K n) x)) = qht x
    rw [← hγ]
    exact qht_mul_left _ γ.2 x
  rw [h]
  exact measurable_qht
