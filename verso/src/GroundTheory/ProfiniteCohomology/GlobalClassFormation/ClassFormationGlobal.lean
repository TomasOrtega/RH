import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

def SumInvRestriction : Prop :=
  ∀ (K F : FiniteSubfield) [Fact (K ≤ F)] (ιK : LocalEmbeddings K) (ιF : LocalEmbeddings F)
    (y : cohomology (limitRep K) 2),
    idelesSumInv ιF ((idelesResField K F 2).hom y) = Module.finrank K.1 F.1 • idelesSumInv ιK y

/- English proof (translation)
Establish `h` using `cohomologyMap_f_comp_g (S := idelesShortComplexRes K) 2`. Conclude with `congrArg (fun f => f.hom x) h`.
-/
theorem idelesToClasses_unitsToIdeles (K : FiniteSubfield) (x : cohomology (unitsLimitRep K) 2) :
    (idelesToClasses K 2).hom ((unitsToIdeles K 2).hom x) = 0 := by
  have h := cohomologyMap_f_comp_g (S := idelesShortComplexRes K) 2
  exact congrArg (fun f => f.hom x) h

section Split

variable (K F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

/- English proof (translation)
Establish `: IsGalois K.1 F.1` using `isGalois_of_normal`. Establish `hle : F.1.fixingSubgroup ≤ K.1.fixingSubgroup` using `IntermediateField.fixingSubgroup_le (Fact.out : K ≤ F)`. Establish `: DiscreteTopology (K.1.fixingSubgroup ⧸ F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup)` using `QuotientGroup.discreteTopology (F.1.fixingSubgroup_isOpen.preimage continuous_subtype_val)`. Establish `hfac : classLevelInfl K F 2 = cohomologyMapAlong (quotGalEquiv K F).toMonoidHom continuous_of_discreteTopology (classInvMor K F) 2 ≫ cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2`. Rewrite using `[classLevelInfl, cohomologyInfl_eq, ← cohomologyMapAlong_comp]`.

Conclude with `cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => rfl) (fun _ => rfl) 2`. Establish `h0 : (cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom ((classLevelInfl K F 2).hom y) = 0`. Establish `h : cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫ cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 = 0` using `cohomologyInfl_comp_cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 1`. Rewrite using `[hfac, ModuleCat.hom_comp, LinearMap.comp_apply]`. Use `show ((cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫ cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom _) = 0`.

Rewrite using `[h]`. Both sides reduce to the same expression. Conclude with `(cohomologyResLE_apply_eq_zero_iff hle classRep 2 _).2 h0`.
-/
theorem classResField_classLevelInfl (y : cohomology (ideleClassRep K.1 F.1) 2) :
    (classResField K F 2).hom ((classLevelInfl K F 2).hom y) = 0 := by
  have : IsGalois K.1 F.1 := isGalois_of_normal
  have hle : F.1.fixingSubgroup ≤ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fact.out : K ≤ F)
  have : DiscreteTopology (K.1.fixingSubgroup ⧸ F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) :=
    QuotientGroup.discreteTopology (F.1.fixingSubgroup_isOpen.preimage continuous_subtype_val)
  have hfac : classLevelInfl K F 2 =
      cohomologyMapAlong (quotGalEquiv K F).toMonoidHom continuous_of_discreteTopology (classInvMor K F) 2 ≫
        cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 := by
    rw [classLevelInfl, cohomologyInfl_eq, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => rfl) (fun _ => rfl) 2
  have h0 : (cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom
      ((classLevelInfl K F 2).hom y) = 0 := by
    have h : cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫
        cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 = 0 :=
      cohomologyInfl_comp_cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 1
    rw [hfac, ModuleCat.hom_comp, LinearMap.comp_apply]
    show ((cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫
        cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom _) = 0
    rw [h]
    rfl
  exact (cohomologyResLE_apply_eq_zero_iff hle classRep 2 _).2 h0

end Split

variable (hR : SumInvRestriction)

include hR in

/- English proof (translation)
Introduce `c`. Take `⟨p, z, rfl⟩` from `exists_classLevelInfl_eq 2 c`. Establish `: IsGalois K.1 p.1.1` using `isGalois_of_normal`. Take `⟨ιF⟩` from `nonempty_localEmbeddings p.1`. Use `set N := Module.finrank K.1 p.1.1 with hN`.

Establish `hN0 : N ≠ 0` using `Module.finrank_pos.ne'`. Establish `hM : Nat.card (LinearMap.ker (classResField K p.1 2).hom) ∣ N` using `natCard_ker_classResField_dvd K p.1`. Take `⟨D, hD⟩` from `sumPlaceInv_surjective K (QZ.mk (1 / N))`. Use `set Y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D with hYdef`. Establish `hY : idelesSumInv ι Y = QZ.mk (1 / N)`.

Rewrite using `[idelesSumInv_apply, hYdef, AddEquiv.apply_symm_apply, hD]`. Establish `hT : ∀ k : ℕ, idelesSumInv ι (k • Y) = QZ.mk ((k : ℚ) / N)`. Introduce `k`. Rewrite using `[map_nsmul, hY, ← QZ.mk_nsmul, nsmul_eq_mul, mul_one_div]`. Establish `hmem : ∀ k : ℕ, (idelesToClasses K 2).hom (k • Y) ∈ LinearMap.ker (classResField K p.1 2).hom`.

Introduce `k`. Rewrite using `[LinearMap.mem_ker, ← idelesToClasses_idelesResField]`. Establish `hres : idelesSumInv ιF ((idelesResField K p.1 2).hom (k • Y)) = 0`. Rewrite using `[hR K p.1 ι ιF, hT, ← QZ.mk_nsmul, nsmul_eq_mul, QZ.mk_eq_zero_iff]`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `: (N : ℚ) ≠ 0` using `by exact_mod_cast hN0`. Rewrite using `[← hN]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨x, hx⟩` from `exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ιF _ hres`. Rewrite using `[← hx, idelesToClasses_unitsToIdeles]`. Set `f : Fin N → LinearMap.ker (classResField K p.1 2).hom` to `fun k => ⟨(idelesToClasses K 2).hom ((k : ℕ) • Y), hmem k⟩`. Establish `finj : Function.Injective f`. Introduce `k k' hkk`.

Establish `h1 : (idelesToClasses K 2).hom ((k : ℕ) • Y) = (idelesToClasses K 2).hom ((k' : ℕ) • Y)` using `congrArg Subtype.val hkk`. Establish `key : ∀ a b : Fin N, (b : ℕ) ≤ a → (idelesToClasses K 2).hom ((a : ℕ) • Y) = (idelesToClasses K 2).hom ((b : ℕ) • Y) → a = b`. Introduce `a b hba hab`. Establish `hw : (idelesToClasses K 2).hom (((a : ℕ) - b) • Y) = 0`. Rewrite using `[sub_nsmul _ hba, ← sub_eq_add_neg, map_sub, hab, sub_self]`.

Establish `h2` using `idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hw`. Rewrite `h2` using `[hT]`. Use `eq_zero_of_mk_div_eq_zero (lt_of_le_of_lt (Nat.sub_le _ _) a.2) (by exact_mod_cast h2)` as an intermediate fact. Conclude with `Fin.ext (by omega)`. Break down `le_total (k' : ℕ) k with h | h` into its components or cases.

Conclude with `key k k' h h1`. Conclude with `(key k' k h h1.symm).symm`. Establish `hfin : Finite (LinearMap.ker (classResField K p.1 2).hom)` using `Nat.finite_of_card_ne_zero (fun h0 => hN0 (by rw [h0, zero_dvd_iff] at hM; exact hM))`. Establish `hcardFin : Nat.card (Fin N) = N` using `Nat.card_eq_fintype_card.trans (Fintype.card_fin N)`. Establish `fsurj` using `(finj.bijective_of_nat_card_le (by`.

Rewrite using `[hcardFin]`. Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hM)).2`. Take `⟨k, hk⟩` from `fsurj ⟨(classLevelInfl K p.1 2).hom z, classResField_classLevelInfl K p.1 z⟩`. Conclude with `⟨(k : ℕ) • Y, congrArg Subtype.val hk⟩`.
-/
theorem idelesToClasses_surjective_of (K : FiniteSubfield) (ι : LocalEmbeddings K) :
    Function.Surjective (idelesToClasses K 2).hom := by
  classical
  intro c
  obtain ⟨p, z, rfl⟩ := exists_classLevelInfl_eq 2 c
  have : IsGalois K.1 p.1.1 := isGalois_of_normal
  obtain ⟨ιF⟩ := nonempty_localEmbeddings p.1
  set N := Module.finrank K.1 p.1.1 with hN
  have hN0 : N ≠ 0 := Module.finrank_pos.ne'
  have hM : Nat.card (LinearMap.ker (classResField K p.1 2).hom) ∣ N := natCard_ker_classResField_dvd K p.1
  obtain ⟨D, hD⟩ := sumPlaceInv_surjective K (QZ.mk (1 / N))
  set Y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D with hYdef
  have hY : idelesSumInv ι Y = QZ.mk (1 / N) := by
    rw [idelesSumInv_apply, hYdef, AddEquiv.apply_symm_apply, hD]
  have hT : ∀ k : ℕ, idelesSumInv ι (k • Y) = QZ.mk ((k : ℚ) / N) := by
    intro k
    rw [map_nsmul, hY, ← QZ.mk_nsmul, nsmul_eq_mul, mul_one_div]
  have hmem : ∀ k : ℕ, (idelesToClasses K 2).hom (k • Y) ∈ LinearMap.ker (classResField K p.1 2).hom := by
    intro k
    rw [LinearMap.mem_ker, ← idelesToClasses_idelesResField]
    have hres : idelesSumInv ιF ((idelesResField K p.1 2).hom (k • Y)) = 0 := by
      rw [hR K p.1 ι ιF, hT, ← QZ.mk_nsmul, nsmul_eq_mul, QZ.mk_eq_zero_iff]
      refine ⟨k, ?_⟩
      have : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
      rw [← hN]
      field_simp
      push_cast
      ring
    obtain ⟨x, hx⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ιF _ hres
    rw [← hx, idelesToClasses_unitsToIdeles]
  let f : Fin N → LinearMap.ker (classResField K p.1 2).hom := fun k =>
    ⟨(idelesToClasses K 2).hom ((k : ℕ) • Y), hmem k⟩
  have finj : Function.Injective f := by
    intro k k' hkk
    have h1 : (idelesToClasses K 2).hom ((k : ℕ) • Y) = (idelesToClasses K 2).hom ((k' : ℕ) • Y) :=
      congrArg Subtype.val hkk
    have key : ∀ a b : Fin N, (b : ℕ) ≤ a →
        (idelesToClasses K 2).hom ((a : ℕ) • Y) = (idelesToClasses K 2).hom ((b : ℕ) • Y) → a = b := by
      intro a b hba hab
      have hw : (idelesToClasses K 2).hom (((a : ℕ) - b) • Y) = 0 := by
        rw [sub_nsmul _ hba, ← sub_eq_add_neg, map_sub, hab, sub_self]
      have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hw
      rw [hT] at h2
      have := eq_zero_of_mk_div_eq_zero (lt_of_le_of_lt (Nat.sub_le _ _) a.2) (by exact_mod_cast h2)
      exact Fin.ext (by omega)
    rcases le_total (k' : ℕ) k with h | h
    · exact key k k' h h1
    · exact (key k' k h h1.symm).symm
  have hfin : Finite (LinearMap.ker (classResField K p.1 2).hom) :=
    Nat.finite_of_card_ne_zero (fun h0 => hN0 (by rw [h0, zero_dvd_iff] at hM; exact hM))
  have hcardFin : Nat.card (Fin N) = N := Nat.card_eq_fintype_card.trans (Fintype.card_fin N)
  have fsurj := (finj.bijective_of_nat_card_le (by
    rw [hcardFin]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hM)).2
  obtain ⟨k, hk⟩ := fsurj ⟨(classLevelInfl K p.1 2).hom z, classResField_classLevelInfl K p.1 z⟩
  exact ⟨(k : ℕ) • Y, congrArg Subtype.val hk⟩

def classInv (K : FiniteSubfield) (ι : LocalEmbeddings K) : cohomology (classLimitRep K) 2 →+ QZ :=
  (QuotientAddGroup.lift (idelesToClasses K 2).hom.toAddMonoidHom.ker (idelesSumInv ι)
    fun y hy => idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι y hy).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom
      (idelesToClasses_surjective_of hR K ι)).symm.toAddMonoidHom

/- English proof (translation)
Establish `h : (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom (idelesToClasses_surjective_of hR K ι)).symm ((idelesToClasses K 2).hom y) = (QuotientAddGroup.mk y : _ ⧸ (idelesToClasses K 2).hom.toAddMonoidHom.ker)`. Rewrite using `[AddEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [classInv, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]`. Both sides reduce to the same expression.
-/
theorem classInv_idelesToClasses (K : FiniteSubfield) (ι : LocalEmbeddings K) (y : cohomology (limitRep K) 2) :
    classInv hR K ι ((idelesToClasses K 2).hom y) = idelesSumInv ι y := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom
      (idelesToClasses_surjective_of hR K ι)).symm ((idelesToClasses K 2).hom y) =
      (QuotientAddGroup.mk y : _ ⧸ (idelesToClasses K 2).hom.toAddMonoidHom.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [classInv, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `(injective_iff_map_eq_zero _).2 fun c hc => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `idelesToClasses_surjective_of hR K ι c`. Rewrite `hc` using `[classInv_idelesToClasses]`. Take `⟨x, rfl⟩` from `exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ι y hc`.

Conclude with `idelesToClasses_unitsToIdeles K x`. Introduce `q`. Take `⟨D, hD⟩` from `sumPlaceInv_surjective K q`. Use `⟨(idelesToClasses K 2).hom ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D), ?_⟩` and prove the remaining obligations. Rewrite using `[classInv_idelesToClasses, idelesSumInv_apply, AddEquiv.apply_symm_apply, hD]`.
-/
theorem classInv_bijective (K : FiniteSubfield) (ι : LocalEmbeddings K) : Function.Bijective (classInv hR K ι) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    obtain ⟨y, rfl⟩ := idelesToClasses_surjective_of hR K ι c
    rw [classInv_idelesToClasses] at hc
    obtain ⟨x, rfl⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ι y hc
    exact idelesToClasses_unitsToIdeles K x
  · intro q
    obtain ⟨D, hD⟩ := sumPlaceInv_surjective K q
    refine ⟨(idelesToClasses K 2).hom ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D), ?_⟩
    rw [classInv_idelesToClasses, idelesSumInv_apply, AddEquiv.apply_symm_apply, hD]

/- English proof (translation)
Take `⟨y, rfl⟩` from `idelesToClasses_surjective_of hR K ιK c`. Rewrite using `[← idelesToClasses_idelesResField, classInv_idelesToClasses, classInv_idelesToClasses, hR K F ιK ιF]`.
-/
theorem classInv_classResField (K F : FiniteSubfield) [Fact (K ≤ F)] (ιK : LocalEmbeddings K)
    (ιF : LocalEmbeddings F) (c : cohomology (classLimitRep K) 2) :
    classInv hR F ιF ((classResField K F 2).hom c) = Module.finrank K.1 F.1 • classInv hR K ιK c := by
  obtain ⟨y, rfl⟩ := idelesToClasses_surjective_of hR K ιK c
  rw [← idelesToClasses_idelesResField, classInv_idelesToClasses, classInv_idelesToClasses, hR K F ιK ιF]

def globalClassFormationOf (K : FiniteSubfield) : ClassFormation (classLimitRep K) where
  inv U := (classInv hR (fieldOf U) (Classical.choice (nonempty_localEmbeddings _))).comp
    (classOpenIso U 2).hom.hom.toAddMonoidHom
  isZero_H1_open_subgroups U := (isZero_cohomology_one_classLimitRep (fieldOf U)).of_iso (classOpenIso U 1)
  inv_res U V h x := by
    have : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
    have hsq := congrArg (fun f => f.hom x) (cohomologyResLE_classOpenIso h 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hsq, classInv_classResField, relIndex_eq_finrank_fieldOf h]
  inv_bijective U := (classInv_bijective hR _ _).comp
    ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

end

end GroundTheory.ProfCoh
