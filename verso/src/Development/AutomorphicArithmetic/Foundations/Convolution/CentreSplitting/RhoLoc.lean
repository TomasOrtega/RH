import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Use `Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _`. Rewrite using `[AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same]`. Conclude with `(congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL v g)).symm`. Rewrite using `[Pi.mulSingle_eq_of_ne h]`. Conclude with `(congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL_of_ne h g)).symm`.
-/
private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  classical
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL_of_ne h g)).symm

/- English proof (translation)
Rewrite using `[← Fb.finEmb_eq]`. Conclude with `Subtype.ext rfl`.
-/
private theorem finProj_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (u : AdelicGLn.FiniteAdelicGL K n) :
    MultiplicityOne.finProj K n u = retractOne (finGL K n u) := by
  rw [← Fb.finEmb_eq]
  exact Subtype.ext rfl

/- English proof (translation)
Introduce `K _ _ n μ _ w g v`. Express the relevant statement in the definitionally equal form `rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v = rightRegularRep (rationalGLOne K n) μ (retractOne (finGL K n (locGL K n w g))) v`. Rewrite using `[finProj_eq, localEmbedding_eq]`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.rhoLoc :
    UpperTheory.ConvolutionTheory.Dp.RhoLoc := by
  intro K _ _ n μ _ w g v
  change rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v =
    rightRegularRep (rationalGLOne K n) μ (retractOne (finGL K n (locGL K n w g))) v
  rw [finProj_eq, localEmbedding_eq]
