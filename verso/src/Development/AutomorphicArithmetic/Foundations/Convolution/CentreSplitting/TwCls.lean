import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `K _ _ n μ _ θ φ hφ ψ hψ`. Establish `hmemS : ∀ g, θ.e.symm g ∈ rationalGLOne K n ↔ g ∈ rationalGLOne K n` using `fun g => by`. Establish `h` using `θ.mem_gam (θ.e.symm g)`. Rewrite `h` using `[ContinuousMulEquiv.apply_symm_apply]`. Conclude with `h.symm`.

Establish `hpresS : MeasurePreserving θ.e.symm μ μ` using `MeasurePreserving.symm θ.e.toHomeomorph.toMeasurableEquiv θ.pres`. Take `⟨hmk, hT⟩` from `UpperTheory.ConvolutionTheory.K.qmapPres (rationalGLOne K n) μ θ.e.symm hmemS hpresS`. Set `T : RightCosetSpace (rationalGLOne K n) → RightCosetSpace (rationalGLOne K n)` to `fun y => mk _ (θ.e.symm (Quotient.out y))`. Establish `hTmk : ∀ x, T (mk _ x) = mk _ (θ.e.symm x)` using `hmk`. Establish `hTc : Continuous T`.

Use `(isOpenQuotientMap_mk (rationalGLOne K n)).isQuotientMap.continuous_iff.2 ?_` and prove the remaining obligations. Establish `h : T ∘ mk _ = mk _ ∘ θ.e.symm` using `funext hTmk`. Rewrite using `[h]`. Conclude with `(continuous_mk _).comp θ.e.symm.continuous`. Set `Φ` to `cuspQuot φ.2.1.isLeftInvariant`.

Set `Ψ` to `cuspQuot ψ.2.1.isLeftInvariant`. Establish `hΦc : Continuous Φ` using `continuous_cuspQuot _ φ.2.1.continuous`. Establish `hΨc : Continuous Ψ` using `continuous_cuspQuot _ ψ.2.1.continuous`. Establish `hb` using `(UpperTheory.ConvolutionTheory.Dp.clsBasic K n μ).2.2.2`. Establish `hout : ∀ (χ : cuspForms K n) (y : RightCosetSpace (rationalGLOne K n)), χ.1 ((Quotient.out y : normOneGL K n) : AdelicGLn.AdelicGL K n) = cuspQuot χ.2.1.isLeftInvariant y` using `fun χ y => by`.

Establish `h : mk (rationalGLOne K n) (Quotient.out y) = y` using `Quotient.out_eq y`. Use `conv_rhs => rw [← h]`. Rewrite using `[cuspQuot_mk]`. Establish `hφa : (clsL μ φ : RightCosetSpace (rationalGLOne K n) → ℂ) =ᵐ[quotientMeasure (rationalGLOne K n) μ] Φ` using `(hb φ hφ).trans (Filter.Eventually.of_forall (hout φ))`. Establish `hψa : (clsL μ ψ : RightCosetSpace (rationalGLOne K n) → ℂ) =ᵐ[quotientMeasure (rationalGLOne K n) μ] Ψ` using `(hb ψ hψ).trans (Filter.Eventually.of_forall (hout ψ))`.

Establish `hU : (θ.U (clsL μ ψ) : RightCosetSpace (rationalGLOne K n) → ℂ) =ᵐ[quotientMeasure (rationalGLOne K n) μ] Ψ ∘ T` using `(θ.U_spec _).trans (hT.quasiMeasurePreserving.ae_eq_comp hψa)`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Establish `h1 : Ψ ∘ T =ᵐ[quotientMeasure (rationalGLOne K n) μ] Φ`. Rewrite `hU` using `[h]`.

Conclude with `hU.symm.trans hφa`. Establish `h2 : Ψ ∘ T = Φ` using `(Continuous.ae_eq_iff_eq _ (hΨc.comp hTc) hΦc).1 h1`. Establish `h3` using `congrFun h2 (mk _ (θ.e x))`. Simplify using `only [Function.comp_apply, hTmk, ContinuousMulEquiv.symm_apply_apply] at h3`. Simplify `h3` using `only [Ψ, Φ, cuspQuot_mk]`.

Introduce `h`. Establish `h2 : Ψ ∘ T = Φ`. Use function extensionality and compare the values at `y`. Take `⟨x, rfl⟩` from `mk_surjective _ y`. Simplify using `only [Function.comp_apply, hTmk, Ψ, Φ, cuspQuot_mk]`.

Rewrite using `[h, ContinuousMulEquiv.apply_symm_apply]`. Rewrite `hU` using `[h2]`. Conclude with `Lp.ext (hU.trans hφa.symm)`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.twCls :
    UpperTheory.ConvolutionTheory.Dp.TwCls := by
  intro K _ _ n μ _ θ φ hφ ψ hψ
  have hmemS : ∀ g, θ.e.symm g ∈ rationalGLOne K n ↔ g ∈ rationalGLOne K n := fun g => by
    have h := θ.mem_gam (θ.e.symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  have hpresS : MeasurePreserving θ.e.symm μ μ :=
    MeasurePreserving.symm θ.e.toHomeomorph.toMeasurableEquiv θ.pres
  obtain ⟨hmk, hT⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (rationalGLOne K n) μ θ.e.symm hmemS hpresS
  let T : RightCosetSpace (rationalGLOne K n) → RightCosetSpace (rationalGLOne K n) :=
    fun y => mk _ (θ.e.symm (Quotient.out y))
  have hTmk : ∀ x, T (mk _ x) = mk _ (θ.e.symm x) := hmk
  have hTc : Continuous T := by
    refine (isOpenQuotientMap_mk (rationalGLOne K n)).isQuotientMap.continuous_iff.2 ?_
    have h : T ∘ mk _ = mk _ ∘ θ.e.symm := funext hTmk
    rw [h]
    exact (continuous_mk _).comp θ.e.symm.continuous
  let Φ := cuspQuot φ.2.1.isLeftInvariant
  let Ψ := cuspQuot ψ.2.1.isLeftInvariant
  have hΦc : Continuous Φ := continuous_cuspQuot _ φ.2.1.continuous
  have hΨc : Continuous Ψ := continuous_cuspQuot _ ψ.2.1.continuous
  have hb := (UpperTheory.ConvolutionTheory.Dp.clsBasic K n μ).2.2.2
  have hout : ∀ (χ : cuspForms K n) (y : RightCosetSpace (rationalGLOne K n)),
      χ.1 ((Quotient.out y : normOneGL K n) : AdelicGLn.AdelicGL K n) =
        cuspQuot χ.2.1.isLeftInvariant y := fun χ y => by
    have h : mk (rationalGLOne K n) (Quotient.out y) = y := Quotient.out_eq y
    conv_rhs => rw [← h]
    rw [cuspQuot_mk]
  have hφa : (clsL μ φ : RightCosetSpace (rationalGLOne K n) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne K n) μ] Φ :=
    (hb φ hφ).trans (Filter.Eventually.of_forall (hout φ))
  have hψa : (clsL μ ψ : RightCosetSpace (rationalGLOne K n) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne K n) μ] Ψ :=
    (hb ψ hψ).trans (Filter.Eventually.of_forall (hout ψ))
  have hU : (θ.U (clsL μ ψ) : RightCosetSpace (rationalGLOne K n) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne K n) μ] Ψ ∘ T :=
    (θ.U_spec _).trans (hT.quasiMeasurePreserving.ae_eq_comp hψa)
  constructor
  · intro h x
    have h1 : Ψ ∘ T =ᵐ[quotientMeasure (rationalGLOne K n) μ] Φ := by
      rw [h] at hU
      exact hU.symm.trans hφa
    have h2 : Ψ ∘ T = Φ := (Continuous.ae_eq_iff_eq _ (hΨc.comp hTc) hΦc).1 h1
    have h3 := congrFun h2 (mk _ (θ.e x))
    simp only [Function.comp_apply, hTmk, ContinuousMulEquiv.symm_apply_apply] at h3
    simpa only [Ψ, Φ, cuspQuot_mk] using h3
  · intro h
    have h2 : Ψ ∘ T = Φ := by
      funext y
      obtain ⟨x, rfl⟩ := mk_surjective _ y
      simp only [Function.comp_apply, hTmk, Ψ, Φ, cuspQuot_mk]
      rw [h, ContinuousMulEquiv.apply_symm_apply]
    rw [h2] at hU
    exact Lp.ext (hU.trans hφa.symm)
