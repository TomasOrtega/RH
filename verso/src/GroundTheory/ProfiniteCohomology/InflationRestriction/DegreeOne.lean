import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
import GroundTheory.ProfiniteCohomology.FilteredHomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

universe u

section Complex

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℕ)

/- English proof (translation)
Establish `h` using `homologyπ_eq_zero_iff K z`. Rewrite `h` using `[CochainComplex.prev_nat_succ]`. Conclude with `h`.
-/
theorem homologyπ_succ_eq_zero_iff (n : ℕ) (z : K.cycles (n + 1)) :
    (K.homologyπ (n + 1)).hom z = 0 ↔
      ∃ w : K.X n, (K.d n (n + 1)).hom w = (K.iCycles (n + 1)).hom z := by
  have h := homologyπ_eq_zero_iff K z
  rw [CochainComplex.prev_nat_succ] at h
  exact h

/- English proof (translation)
Use `exists_iCycles_eq K x ?_` and prove the remaining obligations. Rewrite using `[CochainComplex.next]`. Conclude with `hx`.
-/
theorem exists_iCycles_eq_of_d_eq_zero (n : ℕ) (x : K.X n) (hx : (K.d n (n + 1)).hom x = 0) :
    ∃ z : K.cycles n, (K.iCycles n).hom z = x := by
  refine exists_iCycles_eq K x ?_
  rw [CochainComplex.next]
  exact hx

/- English proof (translation)
The claim follows from `(ModuleCat.epi_iff_surjective _).1 inferInstance`.
-/
theorem homologyπ_surjective (n : ℕ) : Function.Surjective (K.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/- English proof (translation)
The claim follows from `(ModuleCat.mono_iff_injective _).1 inferInstance`.
-/
theorem iCycles_injective (n : ℕ) : Function.Injective (K.iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

end Complex

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Comparison

variable (A : Rep.{u} k G) [IsDiscreteRep A]

omit [IsTopologicalGroup G] in

/- English proof (translation)
Establish `h : w = fun _ => w Fin.elim0` using `funext fun x => congrArg w (Subsingleton.elim _ _)`. Rewrite using `[h]`. Conclude with `IsLocallyConstant.const _`.
-/
theorem isLocallyConstant_cochain_zero (w : (Fin 0 → G) → A) : IsLocallyConstant w := by
  have h : w = fun _ => w Fin.elim0 := funext fun x => congrArg w (Subsingleton.elim _ _)
  rw [h]
  exact IsLocallyConstant.const _

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `h hh`. Take `⟨z, rfl⟩` from `homologyπ_surjective (cochainsComplex A) 1 h`. Establish `hh' : (HomologicalComplex.homologyMap (cochainsComplexι A) 1).hom (((cochainsComplex A).homologyπ 1).hom z) = 0` using `hh`. Rewrite `hh'` using `[homologyMap_homologyπ_apply]`.

Take `⟨w, hw⟩` from `(homologyπ_succ_eq_zero_iff _ 0 _).1 hh'`. Rewrite `hw` using `[iCycles_cyclesMap_apply]`. Use `(homologyπ_succ_eq_zero_iff (cochainsComplex A) 0 z).2 ⟨⟨w, isLocallyConstant_cochain_zero A w⟩, ?_⟩` and prove the remaining obligations. Conclude with `(ModuleCat.mono_iff_injective ((cochainsComplexι A).f 1)).1 inferInstance ((hom_f_d_apply (cochainsComplexι A) 0 1 _).trans hw)`.
-/
theorem cohomologyToGroupCohomology_one_injective :
    Function.Injective (cohomologyToGroupCohomology A 1).hom := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochainsComplex A) 1 h
  have hh' : (HomologicalComplex.homologyMap (cochainsComplexι A) 1).hom
      (((cochainsComplex A).homologyπ 1).hom z) = 0 := hh
  rw [homologyMap_homologyπ_apply] at hh'
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 _).1 hh'
  rw [iCycles_cyclesMap_apply] at hw
  refine (homologyπ_succ_eq_zero_iff (cochainsComplex A) 0 z).2
    ⟨⟨w, isLocallyConstant_cochain_zero A w⟩, ?_⟩
  exact (ModuleCat.mono_iff_injective ((cochainsComplexι A).f 1)).1 inferInstance
    ((hom_f_d_apply (cochainsComplexι A) 0 1 _).trans hw)

end Comparison

section InflationRestriction

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

noncomputable def invariantsIncl :
    Rep.res (1 : N →* PUnit.{u + 1})
        (Rep.res (1 : PUnit.{u + 1} →* G ⧸ N) (A.quotientToInvariants N)) ⟶
      Rep.res N.subtype A :=
  Rep.ofHom ⟨Submodule.subtype _, fun n => by
    ext x
    simp only [LinearMap.comp_apply, MonoidHom.comp_apply, MonoidHom.one_apply, map_one,
      Module.End.one_apply, Submodule.subtype_apply]
    exact (x.2 n).symm⟩

/- English proof (translation)
Set `B` to `Rep.res (1 : PUnit.{u + 1} →* G ⧸ N) (A.quotientToInvariants N)`. Establish `hfac : cochainsMapAlong (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) ≫ cochainsMapAlong N.subtype (continuous_subgroup_subtype N) (𝟙 _) = cochainsMapAlong (A` using `A.quotientToInvariants N) (B := B) 1 continuous_const (𝟙 _) ≫ cochainsMapAlong (A := B) 1 continuous_const (invariantsIncl A N) := by`. Use extensionality with `m x : 3`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `h`.

Express the relevant statement in the definitionally equal form `(((x : locallyConstantCochains (A.quotientToInvariants N) m).1 fun i => ((h i : G) : G ⧸ N)) : A) = (((x : locallyConstantCochains (A.quotientToInvariants N) m).1 fun _ => 1) : A)`. Use `congr 2`. Conclude with `congrArg _ (funext fun i => (QuotientGroup.eq_one_iff _).2 (h i).2)`. Establish `hB : IsZero (cohomology B (n + 1))` using `(isZero_groupCohomology_succ_of_subsingleton B n).of_iso (cohomologyIsoGroupCohomology B (n + 1))`. Express the relevant statement in the definitionally equal form `HomologicalComplex.homologyMap _ (n + 1) ≫ HomologicalComplex.homologyMap _ (n + 1) = 0`.

Rewrite using `[← HomologicalComplex.homologyMap_comp, hfac, HomologicalComplex.homologyMap_comp]`. Establish `h0` using `hB.eq_of_tgt (HomologicalComplex.homologyMap (cochainsMapAlong (A := A.quotientToInvariants N) (B := B) 1 continuous_const (𝟙 _)) (n + 1)) 0`. Rewrite using `[h0]`. Conclude with `Limits.zero_comp`.
-/
theorem cohomologyInfl_comp_cohomologyRes (n : ℕ) :
    cohomologyInfl A N (n + 1) ≫ cohomologyRes A N (n + 1) = 0 := by
  let B := Rep.res (1 : PUnit.{u + 1} →* G ⧸ N) (A.quotientToInvariants N)
  have hfac : cochainsMapAlong (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
        (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) ≫
      cochainsMapAlong N.subtype (continuous_subgroup_subtype N) (𝟙 _) =
      cochainsMapAlong (A := A.quotientToInvariants N) (B := B) 1 continuous_const (𝟙 _) ≫
        cochainsMapAlong (A := B) 1 continuous_const (invariantsIncl A N) := by
    ext m x : 3
    apply Subtype.ext
    funext h
    change (((x : locallyConstantCochains (A.quotientToInvariants N) m).1
        fun i => ((h i : G) : G ⧸ N)) : A) =
      (((x : locallyConstantCochains (A.quotientToInvariants N) m).1 fun _ => 1) : A)
    congr 2
    exact congrArg _ (funext fun i => (QuotientGroup.eq_one_iff _).2 (h i).2)
  have hB : IsZero (cohomology B (n + 1)) :=
    (isZero_groupCohomology_succ_of_subsingleton B n).of_iso (cohomologyIsoGroupCohomology B (n + 1))
  change HomologicalComplex.homologyMap _ (n + 1) ≫ HomologicalComplex.homologyMap _ (n + 1) = 0
  rw [← HomologicalComplex.homologyMap_comp, hfac, HomologicalComplex.homologyMap_comp]
  have h0 := hB.eq_of_tgt (HomologicalComplex.homologyMap (cochainsMapAlong
    (A := A.quotientToInvariants N) (B := B) 1 continuous_const (𝟙 _)) (n + 1)) 0
  rw [h0]
  exact Limits.zero_comp

/- English proof (translation)
Use `congrArg (fun φ => ModuleCat.Hom.hom φ y) (cohomologyInfl_comp_cohomologyToGroupCohomology A N n)` as an intermediate fact. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem map_cohomologyToGroupCohomology_apply (n : ℕ)
    (y : cohomology (A.quotientToInvariants N) n) :
    (groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) n).hom
        ((cohomologyToGroupCohomology (A.quotientToInvariants N) n).hom y) =
      (cohomologyToGroupCohomology A n).hom ((cohomologyInfl A N n).hom y) := by
  have := congrArg (fun φ => ModuleCat.Hom.hom φ y)
    (cohomologyInfl_comp_cohomologyToGroupCohomology A N n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

/- English proof (translation)
Use `congrArg (fun φ => ModuleCat.Hom.hom φ h) (cohomologyRes_comp_cohomologyToGroupCohomology A N n)` as an intermediate fact. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem map_subtype_cohomologyToGroupCohomology_apply (n : ℕ) (h : cohomology A n) :
    (groupCohomology.map N.subtype (𝟙 _) n).hom ((cohomologyToGroupCohomology A n).hom h) =
      (cohomologyToGroupCohomology (Rep.res N.subtype A) n).hom ((cohomologyRes A N n).hom h) := by
  have := congrArg (fun φ => ModuleCat.Hom.hom φ h)
    (cohomologyRes_comp_cohomologyToGroupCohomology A N n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

/- English proof (translation)
Introduce `y y' hyy'`. Establish `hinj : Function.Injective (H1InfRes A N).f.hom` using `(ModuleCat.mono_iff_injective _).1 inferInstance`. Conclude with `cohomologyToGroupCohomology_one_injective _ (hinj ((map_cohomologyToGroupCohomology_apply A N 1 y).trans ((congrArg _ hyy').trans (map_cohomologyToGroupCohomology_apply A N 1 y').symm)))`.
-/
theorem cohomologyInfl_one_injective : Function.Injective (cohomologyInfl A N 1).hom := by
  intro y y' hyy'
  have hinj : Function.Injective (H1InfRes A N).f.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact cohomologyToGroupCohomology_one_injective _ (hinj
    ((map_cohomologyToGroupCohomology_apply A N 1 y).trans ((congrArg _ hyy').trans
      (map_cohomologyToGroupCohomology_apply A N 1 y').symm)))

omit [IsTopologicalGroup G] in

/- English proof (translation)
Introduce `S` and use `hq.isOpen_preimage.mp (hf S)`.
-/
theorem isLocallyConstant_of_comp_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {q : X → Y} (hq : Topology.IsQuotientMap q) {f : Y → Z}
    (hf : IsLocallyConstant (f ∘ q)) : IsLocallyConstant f := fun S =>
  hq.isOpen_preimage.mp (hf S)

/- English proof (translation)
Establish `hg : (groupCohomology.map N.subtype (𝟙 _) 1).hom ((cohomologyToGroupCohomology A 1).hom h) = 0`. Rewrite using `[map_subtype_cohomologyToGroupCohomology_apply, hres, map_zero]`. Establish `hker : (cohomologyToGroupCohomology A 1).hom h ∈ LinearMap.ker (H1InfRes A N).g.hom` using `hg`. Rewrite `hker` using `[← (H1InfRes_exact A N).moduleCat_range_eq_ker]`. Take `⟨y', hy'⟩` from `hker`.

Take `⟨Y, rfl⟩` from `homologyπ_surjective (inhomogeneousCochains (A.quotientToInvariants N)) 1 y'`. Take `⟨z, rfl⟩` from `homologyπ_surjective (cochainsComplex A) 1 h`. Establish `hy0` using `hy'`. Express the relevant statement in the definitionally equal form `(HomologicalComplex.homologyMap (groupCohomology.cochainsMap (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N))) 1).hom (((inhomogeneousCochains (A.quotientToInvariants N)).homologyπ 1).hom Y) = (HomologicalComplex.homologyMap (cochainsComplexι A) 1).hom (((cocha …`. Rewrite `hy'` using `[homologyMap_homologyπ_apply, homologyMap_homologyπ_apply, ← sub_eq_zero, ← map_sub]`.

Take `⟨w, hw⟩` from `(homologyπ_succ_eq_zero_iff _ 0 _).1 hy'`. Rewrite `hw` using `[map_sub, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]`. Set `Yc` to `((inhomogeneousCochains (A.quotientToInvariants N)).iCycles 1).hom Y`. Set `w' : locallyConstantCochains A 0` to `⟨w, isLocallyConstant_cochain_zero A w⟩`. Set `D : locallyConstantCochains A 1` to `((cochainsComplex A).d 0 1).hom w'`.

Set `Z : locallyConstantCochains A 1` to `((cochainsComplex A).iCycles 1).hom z`. Establish `hD : ((cochainsComplexι A).f 1).hom D = (inhomogeneousCochains A).d 0 1 w` using `hom_f_d_apply (cochainsComplexι A) 0 1 w'`. Establish `hF : IsLocallyConstant (((groupCohomology.cochainsMap (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f 1).hom Yc : (Fin 1 → G) → A)`. Rewrite using `[sub_eq_iff_eq_add.mp hw.symm, ← hD]`. Conclude with `D.2.add Z.2`.

Set `q : (Fin 1 → G) → (Fin 1 → G ⧸ N)` to `Pi.map fun _ => QuotientGroup.mk`. Establish `hq : Topology.IsQuotientMap q` using `(IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap`. Establish `hYq : IsLocallyConstant ((Yc : (Fin 1 → G ⧸ N) → _) ∘ q)` using `IsLocallyConstant.desc _ Subtype.val hF Subtype.val_injective`. Establish `hY : IsLocallyConstant (Yc : (Fin 1 → G ⧸ N) → _)` using `isLocallyConstant_of_comp_isQuotientMap hq hYq`. Set `Ylc : locallyConstantCochains (A.quotientToInvariants N) 1` to `⟨Yc, hY⟩`.

Establish `hd : ((cochainsComplex (A.quotientToInvariants N)).d 1 (1 + 1)).hom Ylc = 0`. Apply `(ModuleCat.mono_iff_injective ((cochainsComplexι (A.quotientToInvariants N)).f 2)).1 inferInstance` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `(hom_f_d_apply (cochainsComplexι (A.quotientToInvariants N)) 1 2 Ylc).trans (iCycles_d_apply _ 1 2 Y)`. Take `⟨zY, hzY⟩` from `exists_iCycles_eq_of_d_eq_zero (cochainsComplex (A.quotientToInvariants N)) 1 Ylc hd`.

Use `⟨((cochainsComplex (A.quotientToInvariants N)).homologyπ 1).hom zY, ?_⟩` and prove the remaining obligations. Apply `cohomologyToGroupCohomology_one_injective A` to reduce the goal to its premises. Use `(map_cohomologyToGroupCohomology_apply A N 1 _).symm.trans ?_` and prove the remaining obligations. Establish `hcyc : (HomologicalComplex.cyclesMap (cochainsComplexι (A.quotientToInvariants N)) 1).hom zY = Y`. Apply `iCycles_injective` to reduce the goal to its premises.

Rewrite using `[iCycles_cyclesMap_apply, hzY]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) 1).hom ((HomologicalComplex.homologyMap (cochainsComplexι (A.quotientToInvariants N)) 1).hom (((cochainsComplex (A.quotientToInvariants N)).homologyπ 1).hom zY)) = _`. Rewrite using `[homologyMap_homologyπ_apply, hcyc]`. Conclude with `hy0`.
-/
theorem exists_cohomologyInfl_one_eq (h : cohomology A 1)
    (hres : (cohomologyRes A N 1).hom h = 0) : ∃ y, (cohomologyInfl A N 1).hom y = h := by
  have hg : (groupCohomology.map N.subtype (𝟙 _) 1).hom
      ((cohomologyToGroupCohomology A 1).hom h) = 0 := by
    rw [map_subtype_cohomologyToGroupCohomology_apply, hres, map_zero]
  have hker : (cohomologyToGroupCohomology A 1).hom h ∈ LinearMap.ker (H1InfRes A N).g.hom := hg
  rw [← (H1InfRes_exact A N).moduleCat_range_eq_ker] at hker
  obtain ⟨y', hy'⟩ := hker
  obtain ⟨Y, rfl⟩ := homologyπ_surjective (inhomogeneousCochains (A.quotientToInvariants N)) 1 y'
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochainsComplex A) 1 h
  have hy0 := hy'
  change (HomologicalComplex.homologyMap (groupCohomology.cochainsMap (QuotientGroup.mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))) 1).hom
      (((inhomogeneousCochains (A.quotientToInvariants N)).homologyπ 1).hom Y) =
    (HomologicalComplex.homologyMap (cochainsComplexι A) 1).hom
      (((cochainsComplex A).homologyπ 1).hom z) at hy'
  rw [homologyMap_homologyπ_apply, homologyMap_homologyπ_apply, ← sub_eq_zero, ← map_sub] at hy'
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 _).1 hy'
  rw [map_sub, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply] at hw

  let Yc := ((inhomogeneousCochains (A.quotientToInvariants N)).iCycles 1).hom Y
  let w' : locallyConstantCochains A 0 := ⟨w, isLocallyConstant_cochain_zero A w⟩
  let D : locallyConstantCochains A 1 := ((cochainsComplex A).d 0 1).hom w'
  let Z : locallyConstantCochains A 1 := ((cochainsComplex A).iCycles 1).hom z
  have hD : ((cochainsComplexι A).f 1).hom D = (inhomogeneousCochains A).d 0 1 w :=
    hom_f_d_apply (cochainsComplexι A) 0 1 w'
  have hF : IsLocallyConstant (((groupCohomology.cochainsMap (QuotientGroup.mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f 1).hom Yc : (Fin 1 → G) → A) := by
    rw [sub_eq_iff_eq_add.mp hw.symm, ← hD]
    exact D.2.add Z.2
  let q : (Fin 1 → G) → (Fin 1 → G ⧸ N) := Pi.map fun _ => QuotientGroup.mk
  have hq : Topology.IsQuotientMap q :=
    (IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
  have hYq : IsLocallyConstant ((Yc : (Fin 1 → G ⧸ N) → _) ∘ q) :=
    IsLocallyConstant.desc _ Subtype.val hF Subtype.val_injective
  have hY : IsLocallyConstant (Yc : (Fin 1 → G ⧸ N) → _) :=
    isLocallyConstant_of_comp_isQuotientMap hq hYq
  let Ylc : locallyConstantCochains (A.quotientToInvariants N) 1 := ⟨Yc, hY⟩
  have hd : ((cochainsComplex (A.quotientToInvariants N)).d 1 (1 + 1)).hom Ylc = 0 := by
    apply (ModuleCat.mono_iff_injective ((cochainsComplexι (A.quotientToInvariants N)).f 2)).1
      inferInstance
    rw [map_zero]
    exact (hom_f_d_apply (cochainsComplexι (A.quotientToInvariants N)) 1 2 Ylc).trans
      (iCycles_d_apply _ 1 2 Y)
  obtain ⟨zY, hzY⟩ := exists_iCycles_eq_of_d_eq_zero (cochainsComplex (A.quotientToInvariants N)) 1 Ylc hd
  refine ⟨((cochainsComplex (A.quotientToInvariants N)).homologyπ 1).hom zY, ?_⟩
  apply cohomologyToGroupCohomology_one_injective A
  refine (map_cohomologyToGroupCohomology_apply A N 1 _).symm.trans ?_
  have hcyc : (HomologicalComplex.cyclesMap (cochainsComplexι (A.quotientToInvariants N)) 1).hom zY
      = Y := by
    apply iCycles_injective
    rw [iCycles_cyclesMap_apply, hzY]
    rfl
  change (groupCohomology.map (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N))
      1).hom ((HomologicalComplex.homologyMap (cochainsComplexι (A.quotientToInvariants N)) 1).hom
        (((cochainsComplex (A.quotientToInvariants N)).homologyπ 1).hom zY)) = _
  rw [homologyMap_homologyπ_apply, hcyc]
  exact hy0

end InflationRestriction

end GroundTheory.ProfCoh
