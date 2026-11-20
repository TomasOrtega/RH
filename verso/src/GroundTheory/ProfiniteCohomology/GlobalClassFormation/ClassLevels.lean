import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLimitDefs
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsColimit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.NatCardGroupCohomologyTwoIdeleClassRepDvd
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Level

variable {F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

/- English proof (translation)
The claim follows from `IdeleClassLimit.smul_of_of_normal g c`.
-/
theorem classSmul_of_restrictHom (g : K.1.fixingSubgroup) (c : IdeleClassGroup F.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • IdeleClassLimit.of F c = IdeleClassLimit.of F (restrictHom (E := F) g • c) :=
  IdeleClassLimit.smul_of_of_normal g c

variable (K F) in

def classLevelMor :
    Rep.res (restrictHom (F := K) (E := F)) (ideleClassRep K.1 F.1) ⟶ classLimitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (IdeleClassLimit.of F)).toIntLinearMap, fun g => LinearMap.ext fun x =>
    congrArg Additive.ofMul (classSmul_of_restrictHom g x.toMul).symm⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem classLevelMor_hom_apply (x : Additive (IdeleClassGroup F.1)) :
    (classLevelMor K F).hom x = Additive.ofMul (IdeleClassLimit.of F x.toMul) :=
  rfl

variable (K F) in

def classLevelInfl (n : ℕ) : cohomology (ideleClassRep K.1 F.1) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMapAlong restrictHom continuous_restrictHom (classLevelMor K F) n

end Level

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ideleClassMap (Fact.out : F ≤ E) (ideleClassEquiv ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) c) = ideleClassEquiv ((τ : E.1 ≃ₐ[K.1] E.1) : E.1 ≃+* E.1) (ideleClassMap (Fact.out : F ≤ E) c)`. Set `` to `algebraOfLE (Fact.out : F ≤ E)`. Conclude with `(ideleClassEquiv_ideleClassMap_of_comm ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) (τ : E.1 ≃+* E.1) (fun y ↦ (coe_levelRestrict_apply τ y).symm) c).symm`.
-/
theorem ideleClassMap_smul (τ : E.1 ≃ₐ[K.1] E.1) (c : IdeleClassGroup F.1) :
    ideleClassMap (Fact.out : F ≤ E) (levelRestrict K F E τ • c) =
      τ • ideleClassMap (Fact.out : F ≤ E) c := by
  change ideleClassMap (Fact.out : F ≤ E)
      (ideleClassEquiv ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) c) =
    ideleClassEquiv ((τ : E.1 ≃ₐ[K.1] E.1) : E.1 ≃+* E.1) (ideleClassMap (Fact.out : F ≤ E) c)
  let := algebraOfLE (Fact.out : F ≤ E)
  exact (ideleClassEquiv_ideleClassMap_of_comm ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1)
    (τ : E.1 ≃+* E.1) (fun y ↦ (coe_levelRestrict_apply τ y).symm) c).symm

variable (K F E) in

def classLevelMap : Rep.res (levelRestrict K F E) (ideleClassRep K.1 F.1) ⟶ ideleClassRep K.1 E.1 :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (ideleClassMap (Fact.out : F ≤ E))).toIntLinearMap,
    fun τ => LinearMap.ext fun x => congrArg Additive.ofMul (ideleClassMap_smul τ x.toMul)⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem classLevelMap_hom_apply (x : Additive (IdeleClassGroup F.1)) :
    (classLevelMap K F E).hom x = Additive.ofMul (ideleClassMap (Fact.out : F ≤ E) x.toMul) :=
  rfl

variable (K F E) in

def classLevelTransition (n : ℕ) :
    cohomology (ideleClassRep K.1 F.1) n ⟶ cohomology (ideleClassRep K.1 E.1) n :=
  cohomologyMapAlong (levelRestrict K F E) continuous_levelRestrict (classLevelMap K F E) n

/- English proof (translation)
Rewrite using `[← cochainsMapAlong_comp]`. Use extensionality with `m x : 3`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `Additive.ofMul (IdeleClassLimit.of E (ideleClassMap (Fact.out : F ≤ E) ((x.1 fun i => levelRestrict K F E (restrictHom (E := E) (g i))).toMul))) = Additive.ofMul (IdeleClassLimit.of F ((x.1 fun i => restrictHom (E := F) (g i)).toMul))`.

Establish `hfun : (fun i => levelRestrict K F E (restrictHom (E` using `E) (g i))) = fun i => restrictHom (E := F) (g i) := funext fun i => levelRestrict_restrictHom (g i)`. Use `(congrArg Additive.ofMul (IdeleClassLimit.of_ideleClassMap (Fact.out : F ≤ E) _)).trans ?_` and prove the remaining obligations. Rewrite using `[hfun]`.
-/
theorem classLevelCochains_comp :
    cochainsMapAlong (levelRestrict K F E) continuous_levelRestrict (classLevelMap K F E) ≫
      cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K E) =
      cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K F) := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (IdeleClassLimit.of E (ideleClassMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (restrictHom (E := E) (g i))).toMul))) =
    Additive.ofMul (IdeleClassLimit.of F ((x.1 fun i => restrictHom (E := F) (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (restrictHom (E := E) (g i))) =
      fun i => restrictHom (E := F) (g i) := funext fun i => levelRestrict_restrictHom (g i)
  refine (congrArg Additive.ofMul (IdeleClassLimit.of_ideleClassMap (Fact.out : F ≤ E) _)).trans ?_
  rw [hfun]

/- English proof (translation)
Rewrite using `[classLevelTransition, classLevelInfl, classLevelInfl]`. Unfold `cohomologyMapAlong`. Use `(HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_` and prove the remaining obligations. Rewrite using `[classLevelCochains_comp]`.
-/
theorem classLevelTransition_comp_classLevelInfl (n : ℕ) :
    classLevelTransition K F E n ≫ classLevelInfl K E n = classLevelInfl K F n := by
  rw [classLevelTransition, classLevelInfl, classLevelInfl]
  unfold cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [classLevelCochains_comp]

end Transition

section Colimit

abbrev classLevelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleClassRep K.1 p.1.1) ⟶ cochainsComplex (classLimitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K p.1)

abbrev classLevelCochainsMap {p q : GLevel K} (h : p ≤ q) :
    cochainsComplex (ideleClassRep K.1 p.1.1) ⟶ cochainsComplex (ideleClassRep K.1 q.1.1) :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  cochainsMapAlong (levelRestrict K p.1 q.1) continuous_levelRestrict (classLevelMap K p.1 q.1)

/- English proof (translation)
The claim follows from `haveI : Fact (p.1 ≤ q.1) := ⟨h⟩ classLevelCochains_comp`.
-/
theorem classLevelCochainsMap_comp_classLevelCochainsInfl {p q : GLevel K} (h : p ≤ q) :
    classLevelCochainsMap h ≫ classLevelCochainsInfl q = classLevelCochainsInfl p :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  classLevelCochains_comp

/- English proof (translation)
Introduce `y y' h`. Apply `(ModuleCat.mono_iff_injective ((cochainsComplexι (ideleClassRep K.1 p.1.1)).f m)).1 inferInstance` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Set `σ : Fin m → K.1.fixingSubgroup` to `fun i => Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)`. Establish `hσ : (fun i => restrictHom (E` using `p.1) (σ i)) = τ :=`.

Use function extensionality and compare the values at `fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)`. Establish `h1` using `congrFun (congrArg (fun c => ((cochainsComplexι (classLimitRep K)).f m).hom c) h) σ`. Simplify using `only at h1`. Express the relevant statement in the definitionally equal form `Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y (fun i => restrictHom (E := p.1) (σ i))).toMul) = Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y' (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1`. Rewrite `h1` using `[hσ]`.

Conclude with `congrArg Additive.ofMul (IdeleClassLimit.of_injective p.1 (congrArg Additive.toMul h1))`.
-/
theorem classLevelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((classLevelCochainsInfl p).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (ideleClassRep K.1 p.1.1)).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι (classLimitRep K)).f m).hom c) h) σ
  simp only at h1
  change Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y
      (fun i => restrictHom (E := p.1) (σ i))).toMul) =
    Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y'
      (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1
  rw [hσ] at h1
  exact congrArg Additive.ofMul (IdeleClassLimit.of_injective p.1 (congrArg Additive.toMul h1))

/- English proof (translation)
Establish `hx : IsLocallyConstant (((cochainsComplexι (classLimitRep K)).f m).hom x : (Fin m → K.1.fixingSubgroup) → classLimitRep K)` using `(show locallyConstantCochains (classLimitRep K) m from x).2`. Use `set f := ((cochainsComplexι (classLimitRep K)).f m).hom x with hf`. Take `⟨U, hU⟩` from `exists_openNormalSubgroup_fin_of_isLocallyConstant hx`. Take `⟨t, ht, htU⟩` from `isOpen_induced_iff.1 U.isOpen`. Establish `h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t`.

Establish `: (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t`. Rewrite using `[htU]`. Conclude with `U.one_mem`. Conclude with `this`. Take `⟨E₀, hE₀fin, hE₀⟩` from `(krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)`.

Establish `hfin : (Set.range f).Finite` using `hx.range_finite`. Use `choose idx x' hx' using fun a : classLimitRep K => IdeleClassLimit.exists_of (Additive.toMul a)`. Use `choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E`. Take `⟨p, hp⟩` from `Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪ {lev ⟨E₀, hE₀fin⟩})`. Establish `hpE₀ : E₀ ≤ p.1.1` using `(hlev ⟨E₀, hE₀fin⟩).trans (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))`.

Establish `hker : ∀ g : K.1.fixingSubgroup, restrictHom (E` using `p.1) g = 1 → g ∈ U := by`. Introduce `g hg`. Establish `hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup`. Rewrite using `[← ker_restrictHom, MonoidHom.mem_ker]`. Conclude with `hg`.

Rewrite `hg'` using `[Subgroup.mem_subgroupOf]`. Establish `: g ∈ Subtype.val ⁻¹' t` using `hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')`. Rewrite `this` using `[htU]`. Conclude with `this`. Establish `hval : ∀ g, ∃ z : IdeleClassGroup p.1.1, IdeleClassLimit.of p.1 z = Additive.toMul (f g)`.

Introduce `g`. Establish `hmem : f g ∈ hfin.toFinset` using `by simp`. Establish `hle : idx (f g) ≤ p.1` using `(hlev (idx (f g))).trans (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))`. Conclude with `⟨ideleClassMap hle (x' (f g)), by rw [IdeleClassLimit.of_ideleClassMap]; exact hx' _⟩`. Use `choose z hz using hval`.

Set `lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup` to `fun τ i => Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)`. Use `⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩` and prove the remaining obligations. Apply `(ModuleCat.mono_iff_injective ((cochainsComplexι (classLimitRep K)).f m)).1 inferInstance` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `Additive.ofMul (IdeleClassLimit.of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g`.

Rewrite using `[hz]`. Use `hU _ _ fun i => hker _ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)), inv_mul_cancel]`.
-/
theorem exists_classLevelCochains_eq (m : ℕ) (x : (cochainsComplex (classLimitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleClassRep K.1 p.1.1)).X m),
      ((classLevelCochainsInfl p).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι (classLimitRep K)).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → classLimitRep K) :=
    (show locallyConstantCochains (classLimitRep K) m from x).2
  set f := ((cochainsComplexι (classLimitRep K)).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx x' hx' using fun a : classLimitRep K => IdeleClassLimit.exists_of (Additive.toMul a)
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : IdeleClassGroup p.1.1, IdeleClassLimit.of p.1 z = Additive.toMul (f g) := by
    intro g
    have hmem : f g ∈ hfin.toFinset := by simp
    have hle : idx (f g) ≤ p.1 := (hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    exact ⟨ideleClassMap hle (x' (f g)), by rw [IdeleClassLimit.of_ideleClassMap]; exact hx' _⟩
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (classLimitRep K)).f m)).1 inferInstance
  funext g
  change Additive.ofMul (IdeleClassLimit.of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

/- English proof (translation)
Take `⟨z, rfl⟩` from `(ModuleCat.epi_iff_surjective ((cochainsComplex (classLimitRep K)).homologyπ n)).1 inferInstance x`. Take `⟨p, y₀, hy₀⟩` from `exists_classLevelCochains_eq n (((cochainsComplex (classLimitRep K)).iCycles n).hom z)`. Establish `hd : ((cochainsComplex (ideleClassRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0`. Apply `classLevelCochains_injective p (n + 1)` to reduce the goal to its premises. Rewrite using `[map_zero, hom_f_d_apply, hy₀]`.

Conclude with `iCycles_d_apply _ n (n + 1) z`. Take `⟨w, hw⟩` from `exists_iCycles_eq_of_d_eq_zero _ n y₀ hd`. Use `⟨p, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩` and prove the remaining obligations. Use `(homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).trans (congrArg _ ?_)` and prove the remaining obligations. Apply `(ModuleCat.mono_iff_injective ((cochainsComplex (classLimitRep K)).iCycles n)).1 inferInstance` to reduce the goal to its premises.

Rewrite using `[iCycles_cyclesMap_apply, hw, hy₀]`.
-/
theorem exists_classLevelInfl_eq (n : ℕ) (x : cohomology (classLimitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleClassRep K.1 p.1.1) n), (classLevelInfl K p.1 n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (classLimitRep K)).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_classLevelCochains_eq n
    (((cochainsComplex (classLimitRep K)).iCycles n).hom z)
  have hd : ((cochainsComplex (ideleClassRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0 := by
    apply classLevelCochains_injective p (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (classLimitRep K)).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w = y` from `(ModuleCat.epi_iff_surjective ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n)).1 inferInstance y`. Substitute `hw` using the available equality. Establish `hy'` using `(homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).symm.trans hy`. Take `⟨u, hu⟩` from `(homologyπ_eq_zero_iff _ _).1 hy'`. Rewrite `hu` using `[iCycles_cyclesMap_apply]`.

Take `⟨q, u', hu'⟩` from `exists_classLevelCochains_eq _ u`. Take `⟨r, hpr, hqr⟩` from `GLevel.exists_ge p q`. Use `⟨r, hpr, (homologyMap_homologyπ_apply (classLevelCochainsMap hpr) n w).trans ((homologyπ_eq_zero_iff _ _).2 ⟨((classLevelCochainsMap hqr).f _).hom u', ?_⟩)⟩` and prove the remaining obligations. Rewrite using `[iCycles_cyclesMap_apply]`. Apply `classLevelCochains_injective r n` to reduce the goal to its premises.

Rewrite using `[hom_f_d_apply]`. Establish `e1` using `congrArg (fun φ => (φ.f _).hom u') (classLevelCochainsMap_comp_classLevelCochainsInfl hqr)`. Establish `e2` using `congrArg (fun φ => (φ.f n).hom (((cochainsComplex (ideleClassRep K.1 p.1.1)).iCycles n).hom w)) (classLevelCochainsMap_comp_classLevelCochainsInfl hpr)`. Simplify using `only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2`. Rewrite using `[e1, e2, hu', hu]`.
-/
theorem exists_classLevelTransition_eq_zero (n : ℕ) (p : GLevel K)
    (y : cohomology (ideleClassRep K.1 p.1.1) n) (hy : (classLevelInfl K p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q),
      (HomologicalComplex.homologyMap (classLevelCochainsMap h) n).hom y = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w = y :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n)).1
      inferInstance y
  subst hw
  have hy' := (homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  obtain ⟨q, u', hu'⟩ := exists_classLevelCochains_eq _ u
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  refine ⟨r, hpr, (homologyMap_homologyπ_apply (classLevelCochainsMap hpr) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((classLevelCochainsMap hqr).f _).hom u', ?_⟩)⟩
  rw [iCycles_cyclesMap_apply]
  apply classLevelCochains_injective r n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ => (φ.f _).hom u') (classLevelCochainsMap_comp_classLevelCochainsInfl hqr)
  have e2 := congrArg (fun φ => (φ.f n).hom
      (((cochainsComplex (ideleClassRep K.1 p.1.1)).iCycles n).hom w))
    (classLevelCochainsMap_comp_classLevelCochainsInfl hpr)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1, e2, hu', hu]

end Colimit

variable (K) in

/- English proof (translation)
Rewrite using `[ModuleCat.isZero_iff_subsingleton]`. Establish `hz : ∀ x : cohomology (classLimitRep K) 1, x = 0`. Introduce `x`. Take `⟨p, y, rfl⟩` from `exists_classLevelInfl_eq 1 x`. Establish `h0 : Limits.IsZero (cohomology (ideleClassRep K.1 p.1.1) 1)` using `isZero_groupCohomology_one_ideleClassRep.of_iso (cohomologyIsoGroupCohomology _ 1)`.

Rewrite `h0` using `[ModuleCat.isZero_iff_subsingleton]`. Rewrite using `[Subsingleton.elim y 0, map_zero]`. Conclude with `⟨fun x y => by rw [hz x, hz y]⟩`.
-/
theorem isZero_cohomology_one_classLimitRep : Limits.IsZero (cohomology (classLimitRep K) 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz : ∀ x : cohomology (classLimitRep K) 1, x = 0 := by
    intro x
    obtain ⟨p, y, rfl⟩ := exists_classLevelInfl_eq 1 x
    have h0 : Limits.IsZero (cohomology (ideleClassRep K.1 p.1.1) 1) :=
      isZero_groupCohomology_one_ideleClassRep.of_iso (cohomologyIsoGroupCohomology _ 1)
    rw [ModuleCat.isZero_iff_subsingleton] at h0
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end

end GroundTheory.ProfCoh
