import GroundTheory.AutomorphicForms.L2LocalComponents
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.TensorProductTheorem.Smooth
import Development.WeilBound.CuspidalAdmissibility.OccLocSpan

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace PositivityTheory.TfC.CuspProjectionOrthogonality

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev cuspPart (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))) : Submodule ℂ (CuspL2 μ) :=
  V.comap ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) :
    CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))

/- English proof (translation)
The claim follows from `hcl.preimage (toLp μ).continuous`.
-/
theorem isClosed_cuspPart (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)))
    (hcl : IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)))) :
    IsClosed ((cuspPart μ V : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) :=
  hcl.preimage (toLp μ).continuous

/- English proof (translation)
Introduce `g v hv`. Use `show toLp μ (cuspRepT μ g v) ∈ V`. Rewrite using `[toLp_cuspRepT]`. Conclude with `hinv g _ hv`.
-/
theorem isInvariant_cuspPart (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)))
    (hinv : (rightRegularRep (rationalGLOne K n) μ).IsInvariant V) :
    (cuspRepT μ).IsInvariant (cuspPart μ V) := by
  intro g v hv
  show toLp μ (cuspRepT μ g v) ∈ V
  rw [toLp_cuspRepT]
  exact hinv g _ hv

/- English proof (translation)
The claim follows from `AddMonoidHomClass.isometry_of_norm _ (norm_toLp μ)`.
-/
theorem isometry_toLp (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] :
    Isometry (toLp μ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_toLp μ)

/- English proof (translation)
Use `⟨isClosed_cuspPart μ V hcl, isInvariant_cuspPart μ V hinv, ?_, ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Introduce `h`. Set `u0 : CuspL2 μ` to `⟨u, hle hu⟩`. Establish `hmem : u0 ∈ cuspPart μ V` using `hu`.

Rewrite `hmem` using `[h, Submodule.mem_bot]`. Conclude with `hu0 (congrArg Subtype.val hmem)`. Introduce `U hUc hUi hUV set U' : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) := U.map ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) : CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) with hU'`. Establish `hU'V : U' ≤ V`. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Conclude with `hUV hv`. Establish `hU'c : IsClosed (U' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)))`. Rewrite using `[hU', Submodule.map_coe]`. Conclude with `(isometry_toLp μ).isClosedEmbedding.isClosedMap _ hUc`. Establish `hU'i : (rightRegularRep (rationalGLOne K n) μ).IsInvariant U'`.

Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Conclude with `⟨cuspRepT μ g v, hUi g v hv, rfl⟩`. Break down `hirr U' hU'V hU'c hU'i with h | h` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `v hv`. Establish `: toLp μ v ∈ U'` using `⟨v, hv, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `toLp_injective μ (this.trans (map_zero (toLp μ)).symm)`.

Use `right`. Use `le_antisymm hUV fun v hv => ?_` and prove the remaining obligations. Establish `: toLp μ v ∈ U'` using `by rw [h]; exact hv`. Take `⟨v', hv', e⟩` from `this`. Rewrite using `[← toLp_injective μ e]` and apply the resulting hypothesis.
-/
theorem isMinimal_cuspPart (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)))
    (hle : V ≤ cuspidalL2 μ) (hcl : IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))))
    (hinv : (rightRegularRep (rationalGLOne K n) μ).IsInvariant V) (hne : V ≠ ⊥)
    (hirr : ∀ V' ≤ V, IsClosed (V' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))) →
      (rightRegularRep (rationalGLOne K n) μ).IsInvariant V' → V' = ⊥ ∨ V' = V) :
    (cuspRepT μ).IsMinimal (cuspPart μ V) := by
  refine ⟨isClosed_cuspPart μ V hcl, isInvariant_cuspPart μ V hinv, ?_, ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro h
    let u0 : CuspL2 μ := ⟨u, hle hu⟩
    have hmem : u0 ∈ cuspPart μ V := hu
    rw [h, Submodule.mem_bot] at hmem
    exact hu0 (congrArg Subtype.val hmem)
  · intro U hUc hUi hUV
    set U' : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) :=
      U.map ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) :
        CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) with hU'
    have hU'V : U' ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      exact hUV hv
    have hU'c : IsClosed (U' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))) := by
      rw [hU', Submodule.map_coe]
      exact (isometry_toLp μ).isClosedEmbedding.isClosedMap _ hUc
    have hU'i : (rightRegularRep (rationalGLOne K n) μ).IsInvariant U' := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨cuspRepT μ g v, hUi g v hv, rfl⟩
    rcases hirr U' hU'V hU'c hU'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have : toLp μ v ∈ U' := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact toLp_injective μ (this.trans (map_zero (toLp μ)).symm)
    · right
      refine le_antisymm hUV fun v hv => ?_
      have : toLp μ v ∈ U' := by rw [h]; exact hv
      obtain ⟨v', hv', e⟩ := this
      rwa [← toLp_injective μ e]

section Family

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
  (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule)

def clsL : P.carrier →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ) :=
  ((toLp μ : CuspL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) :
    CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)) ∘ₗ cuspVecL μ ∘ₗ P.carrier.subtype

/- English proof (translation)
Use `show toLp μ (cuspVecL μ (finRepCusp K n h c)) = _`. Rewrite using `[cuspToL2_finRepCusp μ h (P.le_central c.2), toLp_cuspRepT]`. Both sides reduce to the same expression.
-/
theorem clsL_tau (h : AdelicGLn.FiniteAdelicGL K n) (c : P.carrier) :
    clsL μ P (P.toModule.τ h c) =
      rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n h) (clsL μ P c) := by
  show toLp μ (cuspVecL μ (finRepCusp K n h c)) = _
  rw [cuspToL2_finRepCusp μ h (P.le_central c.2), toLp_cuspRepT]
  rfl

variable {P} in
/- English proof (translation)
Use `set E := D.toDecomposition.equiv`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Establish `key : E.toLinearEquiv (P.toModule.fullRep ((1 : FreeMonoid _), h) (E.toLinearEquiv.symm (a ⊗ₜ b))) = RestrictedTensor.outerTensor D.toDecomposition.π₁.rep D.toDecomposition.π₂ ((1 : FreeMonoid _), h) (E.toLinearEquiv (E.toLinearEquiv.symm (a ⊗ₜ b)))` using `LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' ((1 : FreeMonoid _), h)) _`. Rewrite `key` using `[LinearEquiv.apply_symm_apply, RestrictedTensor.outerTensor_tmul]`. Establish `hf : P.toModule.fullRep ((1 : FreeMonoid _), h) (E.toLinearEquiv.symm (a ⊗ₜ b)) = P.toModule.τ h (E.toLinearEquiv.symm (a ⊗ₜ b))` using `by show P.toModule.gk.rep 1 (P.toModule.τ h _) = _`.

Rewrite using `[map_one, Module.End.one_apply]`. Rewrite `key` using `[hf]`. Simplify using `only [map_one, Module.End.one_apply] at key`. Conclude with `key.symm`.
-/
theorem equiv_symm_tmul_tau (h : AdelicGLn.FiniteAdelicGL K n) (a : D.toDecomposition.W₁)
    (b : D.toDecomposition.W₂) :
    D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ D.toDecomposition.π₂ h b) =
      P.toModule.τ h (D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ b)) := by
  set E := D.toDecomposition.equiv
  rw [LinearEquiv.symm_apply_eq]
  have key : E.toLinearEquiv (P.toModule.fullRep ((1 : FreeMonoid _), h) (E.toLinearEquiv.symm (a ⊗ₜ b))) =
      RestrictedTensor.outerTensor D.toDecomposition.π₁.rep D.toDecomposition.π₂ ((1 : FreeMonoid _), h)
        (E.toLinearEquiv (E.toLinearEquiv.symm (a ⊗ₜ b))) :=
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' ((1 : FreeMonoid _), h)) _
  rw [LinearEquiv.apply_symm_apply, RestrictedTensor.outerTensor_tmul] at key
  have hf : P.toModule.fullRep ((1 : FreeMonoid _), h) (E.toLinearEquiv.symm (a ⊗ₜ b)) =
      P.toModule.τ h (E.toLinearEquiv.symm (a ⊗ₜ b)) := by
    show P.toModule.gk.rep 1 (P.toModule.τ h _) = _
    rw [map_one, Module.End.one_apply]
  rw [hf] at key
  simp only [map_one, Module.End.one_apply] at key
  exact key.symm

variable {P} in
/- English proof (translation)
The claim follows from `LinearMap.congr_fun (D.finite.equiv.symm.toIntertwiningMap.isIntertwining' h) t`.
-/
theorem tensorEquiv_symm_rep (h : AdelicGLn.FiniteAdelicGL K n)
    (t : RestrictedTensor.restrictedTensor D.finite.ξ) :
    D.finite.equiv.toLinearEquiv.symm (AdelicGLn.adelicTensorRep D.finite.π D.finite.ξ D.finite.mem_fixedVectors h t) =
      D.toDecomposition.π₂ h (D.finite.equiv.toLinearEquiv.symm t) :=
  LinearMap.congr_fun (D.finite.equiv.symm.toIntertwiningMap.isIntertwining' h) t

open Classical in
variable {P} in

def famL (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) :
    D.finite.W w →ₗ[ℂ] RestrictedTensor.restrictedTensor D.finite.ξ :=
  LinearMap.codRestrict _ ((PiTensorProduct.tprod ℂ).toLinearMap x w) fun y => by
    rw [MultilinearMap.toLinearMap_apply]
    exact RestrictedTensor.tprod_mem_restrictedTensor (hx.update w y)

open Classical in
variable {P} in
/- English proof (translation)
Simplify using `[famL, MultilinearMap.toLinearMap_apply]`.
-/
theorem coe_famL (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) (y : D.finite.W w) :
    (famL D w x hx y : PiTensorProduct ℂ D.finite.W) = PiTensorProduct.tprod ℂ (Function.update x w y) := by
  simp [famL, MultilinearMap.toLinearMap_apply]

variable {P} in
/- English proof (translation)
Rewrite using `[coe_famL]`. Use `congr 1`. Conclude with `Function.update_eq_self w x`.
-/
theorem famL_self (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) :
    (famL D w x hx (x w) : PiTensorProduct ℂ D.finite.W) = PiTensorProduct.tprod ℂ x := by
  classical
  rw [coe_famL]
  congr 1
  exact Function.update_eq_self w x

variable {P} in
/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `hr : AdelicGLn.toRestricted K n (AdelicGLn.localEmbedding w g) = RestrictedProduct.mulSingle (fun v => GLnLocal.integralGL (v.adicCompletion K) n) w g` using `(AdelicGLn.finiteRestrictedEquiv K n).apply_symm_apply _`. Express the relevant statement in the definitionally equal form `_ = RestrictedTensor.tensorRep _ D.finite.π (AdelicGLn.toRestricted K n (AdelicGLn.localEmbedding w g)) (famL D w x hx y : PiTensorProduct ℂ D.finite.W)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Function.update_idem, Function.update_self]`.

Use `_ = RestrictedTensor.tensorRep (fun v => GLnLocal.integralGL (v.adicCompletion K) n) D.finite.π (RestrictedProduct.mulSingle (fun v => GLnLocal.integralGL (v.adicCompletion K) n) w g) (PiTensorProduct.tprod ℂ (Function.update x w y)) := by`. Rewrite using `[RestrictedTensor.tensorRep_mulSingle_tprod]`. Use `_ = _ := congrArg₂ (fun z t => RestrictedTensor.tensorRep (fun v => GLnLocal.integralGL (v.adicCompletion K) n) D.finite.π z t) hr.symm (coe_famL D w x hx y).symm`.
-/
theorem famL_equivariant (w : HeightOneSpectrum (𝓞 K)) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) (g : GL (Fin n) (w.adicCompletion K))
    (y : D.finite.W w) :
    famL D w x hx (D.finite.π w g y) =
      AdelicGLn.adelicTensorRep D.finite.π D.finite.ξ D.finite.mem_fixedVectors
        (AdelicGLn.localEmbedding w g) (famL D w x hx y) := by
  classical
  apply Subtype.ext
  have hr : AdelicGLn.toRestricted K n (AdelicGLn.localEmbedding w g) =
      RestrictedProduct.mulSingle (fun v => GLnLocal.integralGL (v.adicCompletion K) n) w g :=
    (AdelicGLn.finiteRestrictedEquiv K n).apply_symm_apply _
  change _ = RestrictedTensor.tensorRep _ D.finite.π (AdelicGLn.toRestricted K n (AdelicGLn.localEmbedding w g))
    (famL D w x hx y : PiTensorProduct ℂ D.finite.W)
  calc (famL D w x hx (D.finite.π w g y) : PiTensorProduct ℂ D.finite.W)
      = PiTensorProduct.tprod ℂ (Function.update x w (D.finite.π w g y)) := coe_famL D w x hx _
    _ = PiTensorProduct.tprod ℂ (Function.update (Function.update x w y) w
          (D.finite.π w g (Function.update x w y w))) := by
        rw [Function.update_idem, Function.update_self]
    _ = RestrictedTensor.tensorRep (fun v => GLnLocal.integralGL (v.adicCompletion K) n) D.finite.π
          (RestrictedProduct.mulSingle (fun v => GLnLocal.integralGL (v.adicCompletion K) n) w g)
          (PiTensorProduct.tprod ℂ (Function.update x w y)) := by
        rw [RestrictedTensor.tensorRep_mulSingle_tprod]
    _ = _ := congrArg₂ (fun z t => RestrictedTensor.tensorRep
          (fun v => GLnLocal.integralGL (v.adicCompletion K) n) D.finite.π z t) hr.symm (coe_famL D w x hx y).symm

def famF (w : HeightOneSpectrum (𝓞 K)) (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) :
    D.finite.W w →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ) :=
  clsL μ P ∘ₗ D.toDecomposition.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.mk ℂ D.toDecomposition.W₁ D.toDecomposition.W₂ a ∘ₗ
    D.finite.equiv.toLinearEquiv.symm.toLinearMap ∘ₗ famL D w x hx

/- English proof (translation)
Establish `h12` using `(congrArg D.finite.equiv.toLinearEquiv.symm (famL_equivariant D w x hx g y)).trans (tensorEquiv_symm_rep D (AdelicGLn.localEmbedding w g) (famL D w x hx y))`. Establish `h3` using `congrArg (fun t => D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ t)) h12`. Establish `h4` using `h3.trans (equiv_symm_tmul_tau D (AdelicGLn.localEmbedding w g) a (D.finite.equiv.toLinearEquiv.symm (famL D w x hx y)))`. Conclude with `(congrArg (clsL μ P) h4).trans (clsL_tau μ P _ _)`.
-/
theorem famF_equivariant (w : HeightOneSpectrum (𝓞 K)) (a : D.toDecomposition.W₁) (x : ∀ v, D.finite.W v)
    (hx : RestrictedTensor.IsRestricted D.finite.ξ x) (g : GL (Fin n) (w.adicCompletion K))
    (y : D.finite.W w) :
    famF μ P D w a x hx (D.finite.π w g y) = rightRegularRep (rationalGLOne K n) μ
      (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (famF μ P D w a x hx y) := by
  have h12 := (congrArg D.finite.equiv.toLinearEquiv.symm (famL_equivariant D w x hx g y)).trans
    (tensorEquiv_symm_rep D (AdelicGLn.localEmbedding w g) (famL D w x hx y))
  have h3 := congrArg (fun t => D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ t)) h12
  have h4 := h3.trans (equiv_symm_tmul_tau D (AdelicGLn.localEmbedding w g) a
    (D.finite.equiv.toLinearEquiv.symm (famL D w x hx y)))
  exact (congrArg (clsL μ P) h4).trans (clsL_tau μ P _ _)

end Family

/- English proof (translation)
Use `PositivityTheory.TfC.OccursIff.Span.span_core D.finite.ξ D.toDecomposition.equiv.toLinearEquiv D.finite.equiv.toLinearEquiv (clsL μ P) u (fun a x hx => ?_) c` and prove the remaining obligations. Establish `e : famL D w x hx (x w) = ⟨PiTensorProduct.tprod ℂ x, RestrictedTensor.tprod_mem_restrictedTensor hx⟩` using `Subtype.ext (famL_self D w x hx)`. Establish `e2` using `congrArg (fun t => clsL μ P (D.toDecomposition.equiv.toLinearEquiv.symm (a ⊗ₜ D.finite.equiv.toLinearEquiv.symm t))) e`. Conclude with `e2 ▸ h a x hx (x w)`.
-/
theorem inner_clsL_eq_zero (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (P : CuspidalAutomorphicRepresentation K n) (D : AdelicDecomposition P.toModule)
    (w : HeightOneSpectrum (𝓞 K)) (u : Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))
    (h : ∀ a x hx y, inner ℂ (famF μ P D w a x hx y) u = 0) (c : P.carrier) :
    inner ℂ (clsL μ P c) u = 0 := by
  refine PositivityTheory.TfC.OccursIff.Span.span_core D.finite.ξ D.toDecomposition.equiv.toLinearEquiv
    D.finite.equiv.toLinearEquiv (clsL μ P) u (fun a x hx => ?_) c
  have e : famL D w x hx (x w) =
      ⟨PiTensorProduct.tprod ℂ x, RestrictedTensor.tprod_mem_restrictedTensor hx⟩ :=
    Subtype.ext (famL_self D w x hx)
  have e2 := congrArg (fun t => clsL μ P (D.toDecomposition.equiv.toLinearEquiv.symm
    (a ⊗ₜ D.finite.equiv.toLinearEquiv.symm t))) e
  exact e2 ▸ h a x hx (x w)

/- English proof (translation)
Introduce `K _ _ n μ _ V hle hcl hinv hne hirr w`. Establish `: CompleteSpace (cuspPart μ V)` using `(isClosed_cuspPart μ V hcl).completeSpace_coe`. Establish `hV0` using `isInvariant_cuspPart μ V hinv`. Establish `hirr0` using `UnitaryRep.isIrreducible_restrict_of_isMinimal (π := cuspRepT μ) hV0 (isMinimal_cuspPart μ V hle hcl hinv hne hirr)`. Establish `hD` using `CuspidalAutomorphicRepresentation.nonempty_adelicDecomposition_ofL2Summand (cuspPart μ V) hV0 hirr0`.

Use `set P := CuspidalAutomorphicRepresentation.ofL2Summand (cuspPart μ V) hV0 hirr0 with hP`. Take `⟨D⟩` from `hD`. Establish `hmem : ∀ c : P.carrier, clsL μ P c ∈ V` using `fun c => c.2.2`. Use `⟨D.finite.W w, inferInstance, inferInstance, D.finite.π w, D.finite.isAdmissible w, D.finite.isIrreducible w, {f | ∃ a x hx, f = famF μ P D w a x hx}, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨a, x, hx, rfl⟩`.

Conclude with `⟨fun y => hmem _, fun g y => famF_equivariant μ P D w a x hx g y⟩`. Introduce `u hu hu0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `h0 : ∀ a x hx y, inner ℂ (famF μ P D w a x hx y) u = 0` using `fun a x hx y => hall _ ⟨a, x, hx, rfl⟩ y`.

Establish `hc` using `inner_clsL_eq_zero μ P D w u h0`. Set `u0 : CuspL2 μ` to `⟨u, hle hu⟩`. Establish `hu0' : u0 ∈ (P.carrier.map (cuspVecL μ))ᗮ`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce and unpack `_ ⟨c, hc', rfl⟩`.

Conclude with `hc ⟨c, hc'⟩`. Establish `hmemV : u0 ∈ (P.carrier.map (cuspVecL μ)).topologicalClosure`. Rewrite using `[hP, CuspidalAutomorphicRepresentation.topologicalClosure_map_ofL2Summand]`. Conclude with `hu`. Rewrite `hmemV` using `[← Submodule.orthogonal_orthogonal_eq_closure]`.

Establish `h1` using `Submodule.inner_right_of_mem_orthogonal hu0' hmemV`. Rewrite `h1` using `[inner_self_eq_zero]`. Conclude with `hu0 (congrArg Subtype.val h1)`.
-/
theorem occ_loccomp : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))), V ≤ cuspidalL2 μ → IsClosed (V : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V → V ≠ ⊥ → (∀ V' ≤ V, IsClosed (V' : Set (Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ))) → (rightRegularRep (rationalGLOne K n) μ).IsInvariant V' → V' = ⊥ ∨ V' = V) → ∀ (w : HeightOneSpectrum (𝓞 K)), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (π : Representation ℂ (GL (Fin n) (w.adicCompletion K)) W), GroundTheory.Automorphic.IsAdmissible π ∧ π.IsIrreducible ∧ ∃ F : Set (W →ₗ[ℂ] Lp ℂ 2 (quotientMeasure (rationalGLOne K n) μ)), (∀ f ∈ F, (∀ x, f x ∈ V) ∧ ∀ g x, f (π g x) = rightRegularRep (rationalGLOne K n) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (f x)) ∧ ∀ u ∈ V, u ≠ 0 → ∃ f ∈ F, ∃ x, inner ℂ (f x) u ≠ 0 := by
  intro K _ _ n μ _ V hle hcl hinv hne hirr w
  have : CompleteSpace (cuspPart μ V) := (isClosed_cuspPart μ V hcl).completeSpace_coe
  have hV0 := isInvariant_cuspPart μ V hinv
  have hirr0 := UnitaryRep.isIrreducible_restrict_of_isMinimal (π := cuspRepT μ) hV0
    (isMinimal_cuspPart μ V hle hcl hinv hne hirr)
  have hD := CuspidalAutomorphicRepresentation.nonempty_adelicDecomposition_ofL2Summand
    (cuspPart μ V) hV0 hirr0
  set P := CuspidalAutomorphicRepresentation.ofL2Summand (cuspPart μ V) hV0 hirr0 with hP
  obtain ⟨D⟩ := hD
  have hmem : ∀ c : P.carrier, clsL μ P c ∈ V := fun c => c.2.2
  refine ⟨D.finite.W w, inferInstance, inferInstance, D.finite.π w, D.finite.isAdmissible w,
    D.finite.isIrreducible w, {f | ∃ a x hx, f = famF μ P D w a x hx}, ?_, ?_⟩
  · rintro f ⟨a, x, hx, rfl⟩
    exact ⟨fun y => hmem _, fun g y => famF_equivariant μ P D w a x hx g y⟩
  · intro u hu hu0
    by_contra hall
    push_neg at hall
    have h0 : ∀ a x hx y, inner ℂ (famF μ P D w a x hx y) u = 0 :=
      fun a x hx y => hall _ ⟨a, x, hx, rfl⟩ y
    have hc := inner_clsL_eq_zero μ P D w u h0
    let u0 : CuspL2 μ := ⟨u, hle hu⟩
    have hu0' : u0 ∈ (P.carrier.map (cuspVecL μ))ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨c, hc', rfl⟩
      exact hc ⟨c, hc'⟩
    have hmemV : u0 ∈ (P.carrier.map (cuspVecL μ)).topologicalClosure := by
      rw [hP, CuspidalAutomorphicRepresentation.topologicalClosure_map_ofL2Summand]
      exact hu
    rw [← Submodule.orthogonal_orthogonal_eq_closure] at hmemV
    have h1 := Submodule.inner_right_of_mem_orthogonal hu0' hmemV
    rw [inner_self_eq_zero] at h1
    exact hu0 (congrArg Subtype.val h1)

end PositivityTheory.TfC.CuspProjectionOrthogonality
