import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ExistsCoprimeSmulCohomologyTwoGsKernel
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

/- English proof (translation)
The claim follows from `(gsRestrict_gsLift K S).surjective`.
-/
theorem gsRestrict_surjective : Function.Surjective (gsRestrict K S) :=
  (gsRestrict_gsLift K S).surjective

def gsQuotientEquiv : galUnramifiedOutside K.1 ℚ̄ S ≃* K.1.fixingSubgroup ⧸ gsKernel K S :=
  (QuotientGroup.quotientKerEquivOfSurjective (gsRestrict K S) (gsRestrict_surjective K S)).symm

/- English proof (translation)
Rewrite using `[gsQuotientEquiv, MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression.
-/
theorem gsQuotientEquiv_gsRestrict (σ : K.1.fixingSubgroup) :
    gsQuotientEquiv K S (gsRestrict K S σ) = QuotientGroup.mk σ := by
  rw [gsQuotientEquiv, MulEquiv.symm_apply_eq]
  rfl

/- English proof (translation)
Rewrite using `[MulEquiv.symm_apply_eq, gsQuotientEquiv_gsRestrict]`.
-/
theorem gsQuotientEquiv_symm_mk (σ : K.1.fixingSubgroup) :
    (gsQuotientEquiv K S).symm (QuotientGroup.mk σ) = gsRestrict K S σ := by
  rw [MulEquiv.symm_apply_eq, gsQuotientEquiv_gsRestrict]

/- English proof (translation)
Establish `: T2Space (galUnramifiedOutside K.1 ℚ̄ S)` using `galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)`. Conclude with `((continuous_gsRestrict K S).isClosedMap).isQuotientMap (continuous_gsRestrict K S) (gsRestrict_surjective K S)`.
-/
theorem isQuotientMap_gsRestrict : Topology.IsQuotientMap (gsRestrict K S) := by
  have : T2Space (galUnramifiedOutside K.1 ℚ̄ S) := galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
  exact ((continuous_gsRestrict K S).isClosedMap).isQuotientMap (continuous_gsRestrict K S)
    (gsRestrict_surjective K S)

/- English proof (translation)
Rewrite using `[(isQuotientMap_gsRestrict K S).continuous_iff]`. Establish `e : (gsQuotientEquiv K S).toMonoidHom ∘ gsRestrict K S = QuotientGroup.mk' (gsKernel K S)`. Use function extensionality and compare the values at `fun σ => gsQuotientEquiv_gsRestrict K S σ`. Rewrite using `[e]`. Conclude with `continuous_quotientGroup_mk' _`.
-/
theorem continuous_gsQuotientEquiv : Continuous (gsQuotientEquiv K S).toMonoidHom := by
  rw [(isQuotientMap_gsRestrict K S).continuous_iff]
  have e : (gsQuotientEquiv K S).toMonoidHom ∘ gsRestrict K S = QuotientGroup.mk' (gsKernel K S) :=
    funext fun σ => gsQuotientEquiv_gsRestrict K S σ
  rw [e]
  exact continuous_quotientGroup_mk' _

/- English proof (translation)
Rewrite using `[(QuotientGroup.isQuotientMap_mk (gsKernel K S)).continuous_iff]`. Establish `e : (gsQuotientEquiv K S).symm.toMonoidHom ∘ (QuotientGroup.mk : K.1.fixingSubgroup → _) = gsRestrict K S` using `funext fun σ => gsQuotientEquiv_symm_mk K S σ`. Rewrite using `[e]`. Conclude with `continuous_gsRestrict K S`.
-/
theorem continuous_gsQuotientEquiv_symm : Continuous (gsQuotientEquiv K S).symm.toMonoidHom := by
  rw [(QuotientGroup.isQuotientMap_mk (gsKernel K S)).continuous_iff]
  have e : (gsQuotientEquiv K S).symm.toMonoidHom ∘ (QuotientGroup.mk : K.1.fixingSubgroup → _) =
      gsRestrict K S := funext fun σ => gsQuotientEquiv_symm_mk K S σ
  rw [e]
  exact continuous_gsRestrict K S

abbrev unitsInvariantsGsKernel :=
  Representation.invariants ((unitsLimitRep K).ρ.comp (gsKernel K S).subtype)

/- English proof (translation)
Establish `: IsGalois ℚ ℚ̄` using `IsAlgClosure.isGalois ℚ ℚ̄`. Set `KS' : IntermediateField ℚ ℚ̄` to `(maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ`. Establish `h : (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈ IntermediateField.fixedField KS'.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `g hg`.

Establish `hK : g ∈ K.1.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ((maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨y, hy⟩ : K.1))`. Establish `hN : (⟨g, hK⟩ : K.1.fixingSubgroup) ∈ gsKernel K S` using `(mem_gsKernel_iff K S _).2 fun y hy => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy`.

Use `a.2 ⟨⟨g, hK⟩, hN⟩` as an intermediate fact. Conclude with `congrArg (fun z : Additive ℚ̄ˣ => ((Additive.toMul z : ℚ̄ˣ) : ℚ̄)) this`. Rewrite `h` using `[InfiniteGalois.fixedField_fixingSubgroup KS']`. Conclude with `h`.
-/
theorem mem_maxUnramifiedOutside_of_mem_invariantsGsKernel (a : unitsInvariantsGsKernel K S) :
    (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let KS' : IntermediateField ℚ ℚ̄ := (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ
  have h : (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈
      IntermediateField.fixedField KS'.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hK : g ∈ K.1.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ((maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨y, hy⟩ : K.1))
    have hN : (⟨g, hK⟩ : K.1.fixingSubgroup) ∈ gsKernel K S :=
      (mem_gsKernel_iff K S _).2 fun y hy => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy
    have := a.2 ⟨⟨g, hK⟩, hN⟩
    exact congrArg (fun z : Additive ℚ̄ˣ => ((Additive.toMul z : ℚ̄ˣ) : ℚ̄)) this
  rw [InfiniteGalois.fixedField_fixingSubgroup KS'] at h
  exact h

def invariantsGsKernelFun : unitsInvariantsGsKernel K S →+ Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ where
  toFun a := Additive.ofMul (Units.mk0
      (⟨(((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄),
        mem_maxUnramifiedOutside_of_mem_invariantsGsKernel K S a⟩ : maxUnramifiedOutside K.1 ℚ̄ S)
      (fun h => (Additive.toMul (a : Additive ℚ̄ˣ)).ne_zero (congrArg Subtype.val h)))
  map_zero' := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  map_add' _ _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_invariantsGsKernelFun (a : unitsInvariantsGsKernel K S) :
    ((((Additive.toMul (invariantsGsKernelFun K S a)) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) :=
  rfl

/- English proof (translation)
Use `⟨fun a b h => ?_, fun y => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `congrArg (fun z : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ => (((Additive.toMul z : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) h`.

Use `⟨⟨Additive.ofMul (Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom (Additive.toMul y)), fun σ => ?_⟩, ?_⟩` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Establish `hσ` using `(mem_gsKernel_iff K S σ.1).1 σ.2 _ (Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ).1.2`. Conclude with `hσ`.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
theorem invariantsGsKernelFun_bijective : Function.Bijective (invariantsGsKernelFun K S) := by
  refine ⟨fun a b h => ?_, fun y => ?_⟩
  · apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    exact congrArg (fun z : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ =>
      (((Additive.toMul z : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) h
  · refine ⟨⟨Additive.ofMul (Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom
      (Additive.toMul y)), fun σ => ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      apply Units.ext
      have hσ := (mem_gsKernel_iff K S σ.1).1 σ.2 _ (Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ).1.2
      exact hσ
    · apply Additive.toMul.injective
      apply Units.ext
      apply Subtype.ext
      rfl

/- English proof (translation)
Establish `hτ` using `gsRestrict_gsLift K S τ`. Establish `h1 : gsQuotientEquiv K S τ = QuotientGroup.mk (gsLift K S τ)`. Rewrite using `[← gsQuotientEquiv_gsRestrict, hτ]`. Use `(congrArg (fun q => invariantsGsKernelFun K S ((((unitsLimitRep K).quotientToInvariants (gsKernel K S)).ρ q) a)) h1).trans ?_` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2` using `gsRestrict_apply K S (gsLift K S τ) ⟨_, mem_maxUnramifiedOutside_of_mem_invariantsGsKernel K S a⟩`. Rewrite `h2` using `[hτ]`. Conclude with `h2.symm`.
-/
theorem invariantsGsKernelFun_smul (τ : galUnramifiedOutside K.1 ℚ̄ S) (a : unitsInvariantsGsKernel K S) :
    invariantsGsKernelFun K S
        ((((unitsLimitRep K).quotientToInvariants (gsKernel K S)).ρ (gsQuotientEquiv K S τ)) a) =
      (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))).ρ τ (invariantsGsKernelFun K S a) := by
  have hτ := gsRestrict_gsLift K S τ
  have h1 : gsQuotientEquiv K S τ = QuotientGroup.mk (gsLift K S τ) := by
    rw [← gsQuotientEquiv_gsRestrict, hτ]
  refine (congrArg (fun q => invariantsGsKernelFun K S
    ((((unitsLimitRep K).quotientToInvariants (gsKernel K S)).ρ q) a)) h1).trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  have h2 := gsRestrict_apply K S (gsLift K S τ) ⟨_, mem_maxUnramifiedOutside_of_mem_invariantsGsKernel K S a⟩
  rw [hτ] at h2
  exact h2.symm

def invariantsGsKernelMor :
    Rep.res (gsQuotientEquiv K S).toMonoidHom ((unitsLimitRep K).quotientToInvariants (gsKernel K S)) ⟶
      uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  Rep.ofHom ⟨(invariantsGsKernelFun K S).toIntLinearMap, fun τ =>
    LinearMap.ext fun a => invariantsGsKernelFun_smul K S τ a⟩

instance isDiscreteRep_quotientToInvariants_gsKernel :
    IsDiscreteRep ((unitsLimitRep K).quotientToInvariants (gsKernel K S)) :=
  isDiscreteRep_quotientToInvariants_of_normal _ _

instance isIso_cohomologyMapAlong_invariantsGsKernelMor (n : ℕ) :
    IsIso (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom (continuous_gsQuotientEquiv K S)
      (invariantsGsKernelMor K S) n) :=
  isIso_cohomologyMapAlong_of_mulEquiv (gsQuotientEquiv K S) (continuous_gsQuotientEquiv K S)
    (continuous_gsQuotientEquiv_symm K S) _ (invariantsGsKernelFun_bijective K S) n

/- English proof (translation)
Rewrite using `[gsBrauerInfl, ← cohomologyMapAlong_comp, cohomologyInfl]`. Use `cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun σ => gsQuotientEquiv_gsRestrict K S σ) (fun a => ?_) n` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `coe_invariantsGsKernelFun K S a`.
-/
theorem cohomologyMapAlong_invariantsGsKernelMor_comp_gsBrauerInfl (n : ℕ) :
    cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom (continuous_gsQuotientEquiv K S)
      (invariantsGsKernelMor K S) n ≫ gsBrauerInfl K S n =
      cohomologyInfl (unitsLimitRep K) (gsKernel K S) n := by
  rw [gsBrauerInfl, ← cohomologyMapAlong_comp, cohomologyInfl]
  refine cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun σ => gsQuotientEquiv_gsRestrict K S σ)
    (fun a => ?_) n
  apply Additive.toMul.injective
  apply Units.ext
  exact coe_invariantsGsKernelFun K S a

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hsurj : Function.Surjective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) 3).hom` using `(ModuleCat.epi_iff_surjective _).1 inferInstance`. Establish `hinj : Function.Injective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) 3).hom` using `(ModuleCat.mono_iff_injective _).1 inferInstance`. Take `⟨x0, hx0⟩` from `hsurj (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3 x)`. Establish `hk0 : ℓ ^ k • x0 = 0`. Apply `hinj` to reduce the goal to its premises.

Use `(map_nsmul _ (ℓ ^ k) x0).trans ?_` and prove the remaining obligations. Use `(congrArg (fun z => ℓ ^ k • z) hx0).trans ?_` and prove the remaining obligations. Use `(map_nsmul (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3) (ℓ ^ k) x).symm.trans ?_` and prove the remaining obligations. Use `(congrArg _ hx).trans ?_` and prove the remaining obligations. Conclude with `(map_zero _).trans (map_zero _).symm`.

Establish `hinf : (cohomologyInfl (unitsLimitRep K) (gsKernel K S) 3).hom x0 = 0`. Establish `: Subsingleton (cohomology (unitsLimitRep K) 3)` using `subsingleton_cohomology_three_unitsLimitRep K`. Conclude with `Subsingleton.elim _ _`. Establish `h0` using `eq_zero_of_cohomologyInfl_three_eq_zero (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) (isZero_cohomology_one_gsKernel K S) ℓ (exists_coprime_smul_cohomology_two_gsKernel K S hℓ hS) x0 hinf k hk0`. Apply `(cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3).injective` to reduce the goal to its premises.

Rewrite using `[← hx0, h0, map_zero, map_zero]`.
-/
theorem eq_zero_of_h3_gsUnits (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    x = 0 := by
  have hsurj : Function.Surjective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) 3).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) 3).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  obtain ⟨x0, hx0⟩ := hsurj (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3 x)
  have hk0 : ℓ ^ k • x0 = 0 := by
    apply hinj
    refine (map_nsmul _ (ℓ ^ k) x0).trans ?_
    refine (congrArg (fun z => ℓ ^ k • z) hx0).trans ?_
    refine (map_nsmul (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3)
      (ℓ ^ k) x).symm.trans ?_
    refine (congrArg _ hx).trans ?_
    exact (map_zero _).trans (map_zero _).symm
  have hinf : (cohomologyInfl (unitsLimitRep K) (gsKernel K S) 3).hom x0 = 0 := by
    have : Subsingleton (cohomology (unitsLimitRep K) 3) := subsingleton_cohomology_three_unitsLimitRep K
    exact Subsingleton.elim _ _
  have h0 := eq_zero_of_cohomologyInfl_three_eq_zero (unitsLimitRep K) (gsKernel K S)
    (isClosed_gsKernel K S) (isZero_cohomology_one_gsKernel K S) ℓ
    (exists_coprime_smul_cohomology_two_gsKernel K S hℓ hS) x0 hinf k hk0
  apply (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3).injective
  rw [← hx0, h0, map_zero, map_zero]

end

end GroundTheory.ProfCoh
