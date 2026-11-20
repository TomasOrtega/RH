import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.ReductionMahler
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction Formalism.L2.Host
open scoped NumberField.AdeleRing

/- English proof (translation)
Establish `h1 : DenseRange (fun x : WithAbs u.1 => (x : UniformSpace.Completion (WithAbs u.1)))` using `UniformSpace.Completion.denseRange_coe`. Establish `h2 : DenseRange (InfinitePlace.Completion.ofCompletion : _ → u.Completion)` using `(InfinitePlace.Completion.equiv u).symm.surjective.denseRange`. Establish `h3` using `h2.comp h1 (InfinitePlace.Completion.continuous_ofCompletion u)`. Use `h3.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `⟨x.ofAbs, rfl⟩`.
-/
private theorem denseInf {K : Type} [Field K] (u : InfinitePlace K) :
    DenseRange (algebraMap K u.Completion) := by
  have h1 : DenseRange (fun x : WithAbs u.1 => (x : UniformSpace.Completion (WithAbs u.1))) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : DenseRange (InfinitePlace.Completion.ofCompletion : _ → u.Completion) :=
    (InfinitePlace.Completion.equiv u).symm.surjective.denseRange
  have h3 := h2.comp h1 (InfinitePlace.Completion.continuous_ofCompletion u)
  refine h3.mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x.ofAbs, rfl⟩

/- English proof (translation)
The claim follows from `InfinitePlace.Completion.norm_coe (K := K) (v := w) _`.
-/
private theorem normAlg {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x :=
  InfinitePlace.Completion.norm_coe (K := K) (v := w) _

/- English proof (translation)
Establish `h` using `(denseInf (u.comap j.toRingHom)).equalizer (continuous_norm.comp (CT.continuous_infEquiv j u)) continuous_norm (funext fun x => ?_)`. Conclude with `congrFun h y`. Simplify using `only [Function.comp_apply]`. Rewrite using `[CT.infEquiv_algebraMap, normAlg, normAlg]`. Both sides reduce to the same expression.
-/
private theorem norm_infEquiv {K : Type} [Field K] [NumberField K] (j : K ≃+* K) (u : InfinitePlace K)
    (y : (u.comap j.toRingHom).Completion) : ‖CT.infEquiv j u y‖ = ‖y‖ := by
  have h := (denseInf (u.comap j.toRingHom)).equalizer
    (continuous_norm.comp (CT.continuous_infEquiv j u)) continuous_norm (funext fun x => ?_)
  · exact congrFun h y
  simp only [Function.comp_apply]
  rw [CT.infEquiv_algebraMap, normAlg, normAlg]
  rfl

/- English proof (translation)
Establish `h : (u.comap j.toRingHom).IsReal ↔ u.IsReal` using `InfinitePlace.isReal_comap_iff (f := j)`. Unfold `InfinitePlace.mult`. Distinguish the cases in `hu : u.IsReal`. Rewrite using `[if_pos (h.2 hu), if_pos hu]`. Rewrite using `[if_neg (mt h.1 hu), if_neg hu]`.
-/
private theorem mult_comap_equiv {K : Type} [Field K] [NumberField K] (j : K ≃+* K) (u : InfinitePlace K) :
    (u.comap j.toRingHom).mult = u.mult := by
  have h : (u.comap j.toRingHom).IsReal ↔ u.IsReal := InfinitePlace.isReal_comap_iff (f := j)
  unfold InfinitePlace.mult
  by_cases hu : u.IsReal
  · rw [if_pos (h.2 hu), if_pos hu]
  · rw [if_neg (mt h.1 hu), if_neg hu]

private def infPerm {K : Type} [Field K] [NumberField K] (j : K ≃+* K) : InfinitePlace K ≃ InfinitePlace K where
  toFun u := u.comap j.toRingHom
  invFun u := u.comap j.symm.toRingHom
  left_inv u := by
    ext x
    show u (j (j.symm x)) = u x
    rw [RingEquiv.apply_symm_apply]
  right_inv u := by
    ext x
    show u (j.symm (j x)) = u x
    rw [RingEquiv.symm_apply_apply]

private def finPerm {K : Type} [Field K] [NumberField K] (j : K ≃+* K) :
    HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K) where
  toFun v := CT.plMap j.symm v
  invFun v := CT.plMap j v
  left_inv v := CT.plMap_plMap_symm j v
  right_inv v := CT.plMap_symm_plMap j v

/- English proof (translation)
Rewrite using `[GroundTheory.Global.IdeleGroup.ideleModule_eq, GroundTheory.Global.IdeleGroup.ideleModule_eq]`. Use `congr 1`. Use `Fintype.prod_equiv (infPerm σ) _ _ fun u => ?_ show ‖CT.infEquiv σ u ((x : 𝔸[K]).1 (u.comap σ.toRingHom))‖ ^ u.mult = ‖(x : 𝔸[K]).1 (u.comap σ.toRingHom)‖ ^ (u.comap σ.toRingHom).mult` and prove the remaining obligations. Rewrite using `[norm_infEquiv, mult_comap_equiv]`. Establish `h : ∀ v : HeightOneSpectrum (𝓞 K), ‖((Units.map (CT.adMap σ).toMonoidHom x : (𝔸[K])ˣ) : 𝔸[K]).2 v‖ = ‖(x : 𝔸[K]).2 (finPerm σ v)‖` using `fun v => by show ‖(CT.compEquiv σ.symm v).symm ((x : 𝔸[K]).2 (CT.plMap σ.symm v))‖ = _`.

Establish `e` using `CT.norm_compEquiv σ.symm v ((CT.compEquiv σ.symm v).symm ((x : 𝔸[K]).2 (CT.plMap σ.symm v)))`. Rewrite `e` using `[RingEquiv.apply_symm_apply]`. Conclude with `e.symm`. Conclude with `(finprod_congr h).trans (finprod_comp_equiv (finPerm σ) (f := fun w => ‖(x : 𝔸[K]).2 w‖))`.
-/
private theorem module_map {K : Type} [Field K] [NumberField K] (σ : K ≃+* K) (x : (𝔸[K])ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (Units.map (CT.adMap σ).toMonoidHom x) : ℝ) =
      GroundTheory.Global.IdeleGroup.ideleModule K x := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  congr 1
  · refine Fintype.prod_equiv (infPerm σ) _ _ fun u => ?_
    show ‖CT.infEquiv σ u ((x : 𝔸[K]).1 (u.comap σ.toRingHom))‖ ^ u.mult =
      ‖(x : 𝔸[K]).1 (u.comap σ.toRingHom)‖ ^ (u.comap σ.toRingHom).mult
    rw [norm_infEquiv, mult_comap_equiv]
  · have h : ∀ v : HeightOneSpectrum (𝓞 K),
        ‖((Units.map (CT.adMap σ).toMonoidHom x : (𝔸[K])ˣ) : 𝔸[K]).2 v‖ =
          ‖(x : 𝔸[K]).2 (finPerm σ v)‖ := fun v => by
      show ‖(CT.compEquiv σ.symm v).symm ((x : 𝔸[K]).2 (CT.plMap σ.symm v))‖ = _
      have e := CT.norm_compEquiv σ.symm v ((CT.compEquiv σ.symm v).symm ((x : 𝔸[K]).2 (CT.plMap σ.symm v)))
      rw [RingEquiv.apply_symm_apply] at e
      exact e.symm
    exact (finprod_congr h).trans
      (finprod_comp_equiv (finPerm σ) (f := fun w => ‖(x : 𝔸[K]).2 w‖))

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Conclude with `(RingHom.map_det (CT.adMap σ) (g : AdelicGLn.AdelicMatrix K n)).symm`.
-/
private theorem det_map {K : Type} [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n) :
    AdelicGLn.det K n (Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) =
      Units.map (CT.adMap σ).toMonoidHom (AdelicGLn.det K n g) := by
  refine Units.ext ?_
  exact (RingHom.map_det (CT.adMap σ) (g : AdelicGLn.AdelicMatrix K n)).symm

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use `show CT.adMap σ.symm (CT.adMap σ ((g : AdelicGLn.AdelicMatrix K n) a b)) = _`. Rewrite using `[← (UpperTheory.ConvolutionTheory.K.adBasic K).2.2 σ σ.symm, RingEquiv.self_trans_symm]`. Conclude with `(UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _`.
-/
private theorem map_symm_map {K : Type} [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (CT.adMap σ.symm)
      (Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) = g := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  show CT.adMap σ.symm (CT.adMap σ ((g : AdelicGLn.AdelicMatrix K n) a b)) = _
  rw [← (UpperTheory.ConvolutionTheory.K.adBasic K).2.2 σ σ.symm, RingEquiv.self_trans_symm]
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _

/- English proof (translation)
Take `⟨γ, rfl⟩` from `hg`. Use `⟨Matrix.GeneralLinearGroup.map (σ : K →+* K) γ, Units.ext (Matrix.ext fun a b => ?_)⟩` and prove the remaining obligations. Conclude with `((UpperTheory.ConvolutionTheory.K.adBasic K).1 σ _).symm`.
-/
private theorem map_rational {K : Type} [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n)
    (hg : g ∈ AdelicGLn.rationalGL K n) :
    (Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.rationalGL K n := by
  obtain ⟨γ, rfl⟩ := hg
  refine ⟨Matrix.GeneralLinearGroup.map (σ : K →+* K) γ, Units.ext (Matrix.ext fun a b => ?_)⟩
  exact ((UpperTheory.ConvolutionTheory.K.adBasic K).1 σ _).symm

/- English proof (translation)
Introduce `K _ _ n σ g`. Use `⟨?_, fun h => ?_, map_rational n σ g⟩` and prove the remaining obligations. Rewrite using `[mem_normOneGL, mem_normOneGL, det_map, module_map]`. Use `map_rational n σ.symm _ h` as an intermediate fact. Rewrite `this` using `[map_symm_map]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.ConvolutionTheory.K.adNormOne :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n),
      ((Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) ∈ normOneGL K n ↔ g ∈ normOneGL K n) ∧
      ((Matrix.GeneralLinearGroup.map (CT.adMap σ) g : AdelicGLn.AdelicGL K n) ∈ AdelicGLn.rationalGL K n ↔ g ∈ AdelicGLn.rationalGL K n) := by
  intro K _ _ n σ g
  refine ⟨?_, fun h => ?_, map_rational n σ g⟩
  · rw [mem_normOneGL, mem_normOneGL, det_map, module_map]
  · have := map_rational n σ.symm _ h
    rwa [map_symm_map] at this
