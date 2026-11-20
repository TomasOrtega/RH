import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions GlobalTheory.CuspRep
open Filter Topology Matrix GroundTheory.Automorphic GroundTheory.Automorphic.RestrictedTensor GroundTheory.Automorphic.AdelicGLn
open scoped RestrictedProduct

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => rfl)`.
-/
private theorem toRes_apply (g : GL (Fin n) (Af F)) (v : HeightOneSpectrum (𝓞 F)) :
    toRestricted F n g v = GeneralLinearGroup.map (pLoc F v) g := Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations. Rewrite using `[toRes_apply]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[pLoc_locGL, singleHom_apply_self]`.

Rewrite using `[pLoc_locGL_of_ne h, singleHom_apply_of_ne _ h]`.
-/
private theorem toRes_loc [DecidableEq (HeightOneSpectrum (𝓞 F))] (w : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin n) (w.adicCompletion F)) :
    toRestricted F n (locGL F n w g) = singleHom (fun v => GLnLocal.integralGL (v.adicCompletion F) n) w g := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  rw [toRes_apply]
  by_cases h : v = w
  · subst h; rw [pLoc_locGL, singleHom_apply_self]
  · rw [pLoc_locGL_of_ne h, singleHom_apply_of_ne _ h]

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (Af F)) V}

/- English proof (translation)
The claim follows from `congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap g x)`.
-/
private theorem coe_equiv (D : TensorDecomposition F n ρ) (g : GL (Fin n) (Af F)) (x : V) :
    (D.equiv.toLinearEquiv (ρ g x)).1 = tensorRep _ D.π (toRestricted F n g) (D.equiv.toLinearEquiv x).1 :=
  congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ D.equiv.toIntertwiningMap g x)

/- English proof (translation)
Use `choose u hu using fun v => @exists_ne _ (nontrivial_of_isIrreducible (D.isIrreducible v)) 0`. Use `⟨fun v => if D.ξ v = 0 then u v else D.ξ v, D.ne_zero.mono fun v hv => if_neg hv, fun v => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Use `split_ifs with h`. Use `exacts [hu v, h]`.
-/
private theorem exists_vec (D : TensorDecomposition F n ρ) : ∃ η : ∀ v, D.W v, IsRestricted D.ξ η ∧ ∀ v, η v ≠ 0 := by
  classical
  choose u hu using fun v => @exists_ne _ (nontrivial_of_isIrreducible (D.isIrreducible v)) 0
  refine ⟨fun v => if D.ξ v = 0 then u v else D.ξ v, D.ne_zero.mono fun v hv => if_neg hv, fun v => ?_⟩
  beta_reduce
  split_ifs with h
  exacts [hu v, h]

/- English proof (translation)
Take `⟨η, hη, h0⟩` from `exists_vec D`. Set `j : D.W w →ₗ[ℂ] restrictedTensor D.ξ` to `((PiTensorProduct.tprod ℂ).toLinearMap η w).codRestrict _ fun u => tprod_mem_restrictedTensor (hη.update w u)`. Establish `hj : ∀ u, (j u).1 = PiTensorProduct.tprod ℂ (Function.update η w u)` using `fun _ => rfl`. Use `⟨D.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ j, fun e => ?_, fun g x => ?_⟩` and prove the remaining obligations. Establish `h1 : D.equiv.toLinearEquiv.symm (j (η w)) = 0` using `LinearMap.congr_fun e (η w)`.

Establish `h2` using `congrArg Subtype.val (D.equiv.toLinearEquiv.symm.map_eq_zero_iff.1 h1)`. Rewrite `h2` using `[hj, Function.update_eq_self]`. Conclude with `tprod_ne_zero hη h0 h2`. Use `D.equiv.toLinearEquiv.injective (Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[coe_equiv, toRes_loc]`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hj]`. Establish `h3` using `tensorRep_mulSingle_tprod (K := fun v => GLnLocal.integralGL (v.adicCompletion F) n) (π := D.π) w g (Function.update η w x)`. Rewrite `h3` using `[Function.update_idem, Function.update_self]`. Conclude with `h3.symm`.
-/
private theorem exists_emb (D : TensorDecomposition F n ρ) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ f : D.W w →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (D.π w g x) = ρ (locGL F n w g) (f x) := by
  classical
  obtain ⟨η, hη, h0⟩ := exists_vec D
  let j : D.W w →ₗ[ℂ] restrictedTensor D.ξ :=
    ((PiTensorProduct.tprod ℂ).toLinearMap η w).codRestrict _ fun u => tprod_mem_restrictedTensor (hη.update w u)
  have hj : ∀ u, (j u).1 = PiTensorProduct.tprod ℂ (Function.update η w u) := fun _ => rfl
  refine ⟨D.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ j, fun e => ?_, fun g x => ?_⟩
  · have h1 : D.equiv.toLinearEquiv.symm (j (η w)) = 0 := LinearMap.congr_fun e (η w)
    have h2 := congrArg Subtype.val (D.equiv.toLinearEquiv.symm.map_eq_zero_iff.1 h1)
    rw [hj, Function.update_eq_self] at h2
    exact tprod_ne_zero hη h0 h2
  · refine D.equiv.toLinearEquiv.injective (Subtype.ext ?_)
    rw [coe_equiv, toRes_loc]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hj]
    have h3 := tensorRep_mulSingle_tprod (K := fun v => GLnLocal.integralGL (v.adicCompletion F) n) (π := D.π) w g
      (Function.update η w x)
    rw [Function.update_idem, Function.update_self] at h3
    exact h3.symm

end SlopeTestRemainingChoices

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Establish `h2` using `Representation.IntertwiningMap.isIntertwining _ _ D.equiv.symm.toIntertwiningMap (1, g) (u ⊗ₜ y)`. Rewrite `h2` using `[RestrictedTensor.outerTensor_tmul]`. Simplify using `only [map_one, Module.End.one_apply] at h2`. Use `Eq.trans ?_ h2.symm` and prove the remaining obligations. Use `show _ = Mx.gk.rep 1 _`.

Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
private theorem dec_tau {K : Type} [Field K] [NumberField K] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {Mx : AdelicGKModule K n V} (D : Mx.Decomposition) (u : D.W₁) (g : AdelicGLn.FiniteAdelicGL K n) (y : D.W₂) :
    Mx.τ g (D.equiv.toLinearEquiv.symm (u ⊗ₜ y)) = D.equiv.toLinearEquiv.symm (u ⊗ₜ D.π₂ g y) := by
  have h2 := Representation.IntertwiningMap.isIntertwining _ _ D.equiv.symm.toIntertwiningMap (1, g) (u ⊗ₜ y)
  rw [RestrictedTensor.outerTensor_tmul] at h2
  simp only [map_one, Module.End.one_apply] at h2
  refine Eq.trans ?_ h2.symm
  show _ = Mx.gk.rep 1 _
  rw [map_one]; rfl

/- English proof (translation)
Introduce `E _ _ _ n π D w σ`. Take `⟨f, h0, hf⟩` from `exists_emb (F := E) D.finite w`. Establish `hnt : Nontrivial (Cm.carrier π)` using `Submodule.nontrivial_iff_ne_bot.2 fun e => π.ne_bot (by rw [← Cm.map_carrier, e, Submodule.map_bot])`. Set `e` to `D.toDecomposition.equiv`. Establish `h1 : Nontrivial D.toDecomposition.W₁`.

Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_nontrivial_iff_subsingleton]`. Conclude with `not_subsingleton (Cm.carrier π) e.toLinearEquiv.injective.subsingleton`. Take `⟨u, hu⟩` from `exists_ne (0 : D.toDecomposition.W₁)`. Set `J : D.finite.W w →ₗ[ℂ] π.V` to `(Cm.carrierEq π).toLinearMap ∘ₗ e.toLinearEquiv.symm.toLinearMap ∘ₗ TensorProduct.mk ℂ _ _ u ∘ₗ f`.

Establish `hJ0 : ∀ x, J x = 0 → f x = 0` using `fun x hx => by`. Establish `h2 : e.toLinearEquiv.symm (u ⊗ₜ f x) = 0` using `(Cm.carrierEq π).map_eq_zero_iff.1 hx`. Establish `h3` using `e.toLinearEquiv.symm.map_eq_zero_iff.1 h2`. Take `⟨l, hl⟩` from `Module.Projective.exists_dual_eq_one ℂ hu`. Simplify `congrArg (fun z => TensorProduct.lid ℂ _ (LinearMap.rTensor _ l z)) h3` using `[hl]`.

Establish `hJ : ∀ g x, J (D.finite.π w g x) = π.locRep w g (J x)` using `fun g x => by`. Use `Eq.trans ?_ (Cm.carrierEq_τ π (locGL E n w g) _)` and prove the remaining obligations. Use `congrArg (Cm.carrierEq π) ?_` and prove the remaining obligations. Establish `h2` using `dec_tau D.toDecomposition u (locGL E n w g) (f x)`. Rewrite `h2` using `[← hf]`.

Conclude with `h2.symm`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `GlobalTheory.CuspRep.LocUniq.isLocComp_unique π w σ { V := D.finite.W w, ρ := D.finite.π w, smooth := (D.finite.isAdmissible w).1, irred := D.finite.isIrreducible w } h ⟨J, fun h2 => h0 (LinearMap.ext fun x => hJ0 x (LinearMap.congr_fun h2 x)), hJ⟩`. Introduce and unpack `⟨t⟩`.

Use `⟨J ∘ₗ t.toLinearEquiv.toLinearMap, fun h2 => h0 (LinearMap.ext fun x => hJ0 x ?_), fun g x => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `t.toLinearEquiv.surjective x`. Conclude with `LinearMap.congr_fun h2 y`. Conclude with `(congrArg J (Representation.IntertwiningMap.isIntertwining _ _ t.toIntertwiningMap g x)).trans (hJ g _)`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.locFlath :
    UpperTheory.ConvolutionTheory.Dp.LocFlath := by
  intro E _ _ _ n π D w σ
  obtain ⟨f, h0, hf⟩ := exists_emb (F := E) D.finite w
  have hnt : Nontrivial (Cm.carrier π) := Submodule.nontrivial_iff_ne_bot.2 fun e =>
    π.ne_bot (by rw [← Cm.map_carrier, e, Submodule.map_bot])
  let e := D.toDecomposition.equiv
  have h1 : Nontrivial D.toDecomposition.W₁ := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact not_subsingleton (Cm.carrier π) e.toLinearEquiv.injective.subsingleton
  obtain ⟨u, hu⟩ := exists_ne (0 : D.toDecomposition.W₁)
  let J : D.finite.W w →ₗ[ℂ] π.V := (Cm.carrierEq π).toLinearMap ∘ₗ e.toLinearEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.mk ℂ _ _ u ∘ₗ f
  have hJ0 : ∀ x, J x = 0 → f x = 0 := fun x hx => by
    have h2 : e.toLinearEquiv.symm (u ⊗ₜ f x) = 0 := (Cm.carrierEq π).map_eq_zero_iff.1 hx
    have h3 := e.toLinearEquiv.symm.map_eq_zero_iff.1 h2
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hu
    simpa [hl] using congrArg (fun z => TensorProduct.lid ℂ _ (LinearMap.rTensor _ l z)) h3
  have hJ : ∀ g x, J (D.finite.π w g x) = π.locRep w g (J x) := fun g x => by
    refine Eq.trans ?_ (Cm.carrierEq_τ π (locGL E n w g) _)
    refine congrArg (Cm.carrierEq π) ?_
    have h2 := dec_tau D.toDecomposition u (locGL E n w g) (f x)
    rw [← hf] at h2
    exact h2.symm
  constructor
  · intro h
    exact GlobalTheory.CuspRep.LocUniq.isLocComp_unique π w σ
      { V := D.finite.W w, ρ := D.finite.π w, smooth := (D.finite.isAdmissible w).1, irred := D.finite.isIrreducible w } h
      ⟨J, fun h2 => h0 (LinearMap.ext fun x => hJ0 x (LinearMap.congr_fun h2 x)), hJ⟩
  · rintro ⟨t⟩
    refine ⟨J ∘ₗ t.toLinearEquiv.toLinearMap, fun h2 => h0 (LinearMap.ext fun x => hJ0 x ?_), fun g x => ?_⟩
    · obtain ⟨y, rfl⟩ := t.toLinearEquiv.surjective x
      exact LinearMap.congr_fun h2 y
    · exact (congrArg J (Representation.IntertwiningMap.isIntertwining _ _ t.toIntertwiningMap g x)).trans (hJ g _)
