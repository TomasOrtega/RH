import Mathlib
import GroundTheory.LocalFields.LocalReciprocityFinite
import GroundTheory.LocalFields.AbstractLocalReciprocity.NormGroups

namespace GroundTheory.LocalField

open Abstract

section Dictionary

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Rewrite using `[← InfiniteGalois.normal_iff_isGalois, coe_fixingOpenSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations. Use `h.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, Subgroup.mem_top g⟩` as an intermediate fact.

Conclude with `Subgroup.mem_subgroupOf.1 this`. Introduce `h`. Conclude with `h.subgroupOf _`.
-/
theorem normal_subgroupOf_top_fixingOpenSubgroup_iff (L : IntermediateField K Ω)
    [FiniteDimensional K L] :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal ↔ IsGalois K L := by
  rw [← InfiniteGalois.normal_iff_isGalois, coe_fixingOpenSubgroup]
  constructor
  · intro h
    refine ⟨fun n hn g => ?_⟩
    have := h.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, Subgroup.mem_top g⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro h
    exact h.subgroupOf _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hn` using `h.normal`. Establish `hG : IsGalois K L` using `(normal_subgroupOf_top_fixingOpenSubgroup_iff L).1 hn`. Use `⟨hG, fun σ τ => ?_⟩` and prove the remaining obligations.

Establish `hc` using `h.isMulCommutative`. Take `⟨p, rfl⟩` from `(baseQuotientEquiv L).surjective σ`. Take `⟨q, rfl⟩` from `(baseQuotientEquiv L).surjective τ`. Rewrite using `[← map_mul, ← map_mul, hc.is_comm.comm]`. Introduce and unpack `⟨hG, hc⟩`.

Establish `hn` using `(normal_subgroupOf_top_fixingOpenSubgroup_iff L).2 hG`. Establish `: IsMulCommutative (((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)))` using `⟨⟨fun p q => (baseQuotientEquiv L).injective (by rw [map_mul, map_mul, hc])⟩⟩`. Conclude with `isAbelianExtension_of_isMulCommutative le_top`.
-/
theorem isAbelianExtension_fixingOpenSubgroup_iff (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsAbelianExtension ⊤ (fixingOpenSubgroup L) ↔
      IsGalois K L ∧ ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
  constructor
  · intro h
    have hn := h.normal
    have hG : IsGalois K L := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).1 hn
    refine ⟨hG, fun σ τ => ?_⟩
    have hc := h.isMulCommutative
    obtain ⟨p, rfl⟩ := (baseQuotientEquiv L).surjective σ
    obtain ⟨q, rfl⟩ := (baseQuotientEquiv L).surjective τ
    rw [← map_mul, ← map_mul, hc.is_comm.comm]
  · rintro ⟨hG, hc⟩
    have hn := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).2 hG
    have : IsMulCommutative (((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :=
      ⟨⟨fun p q => (baseQuotientEquiv L).injective (by rw [map_mul, map_mul, hc])⟩⟩
    exact isAbelianExtension_of_isMulCommutative le_top

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Establish `: (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex` using `inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, rfl⟩, rfl⟩`. Conclude with `⟨_, (baseUnitsEquiv_norm L a).symm⟩`.

Introduce and unpack `⟨b, rfl⟩`. Use `⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `baseUnitsEquiv (Abstract.norm Ωˣ ⊤ L.fixingSubgroup _) = _`. Rewrite using `[baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]`.
-/
theorem map_baseUnitsEquiv_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (normGroup Ωˣ ⊤ (fixingOpenSubgroup L)).map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  have : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩
    change baseUnitsEquiv (Abstract.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Rewrite using `[← map_baseUnitsEquiv_normGroup L]`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨a, ha, rfl⟩`. Introduce and unpack `⟨b, hb, hba⟩`.

Rewrite using `[← baseUnitsEquiv.injective hba]` and apply the resulting hypothesis.
-/
theorem mem_normGroup_iff_mem_range_normUnits (L : IntermediateField K Ω) [FiniteDimensional K L]
    (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    a ∈ normGroup Ωˣ ⊤ (fixingOpenSubgroup L) ↔ baseUnitsEquiv a ∈ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup L]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, hba⟩
    rwa [← baseUnitsEquiv.injective hba]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Use extensionality with `a`. Conclude with `mem_normGroup_iff_mem_range_normUnits L a`.
-/
theorem normGroup_eq_comap (L : IntermediateField K Ω) [FiniteDimensional K L] :
    normGroup Ωˣ ⊤ (fixingOpenSubgroup L) =
      (normUnits K L).range.comap
        (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) := by
  ext a
  exact mem_normGroup_iff_mem_range_normUnits L a

variable (L : IntermediateField K Ω) [FiniteDimensional K L]

noncomputable def maximalAbelianSubextension : IntermediateField K Ω :=
  IntermediateField.fixedField (maxAbelian (le_top : fixingOpenSubgroup L ≤ ⊤) : Subgroup (Ω ≃ₐ[K] Ω))

instance finiteDimensional_maximalAbelianSubextension :
    FiniteDimensional K (maximalAbelianSubextension L) :=
  finiteDimensional_fixedField_openSubgroup _

/- English proof (translation)
The claim follows from `fixingOpenSubgroup_fixedField _`.
-/
theorem fixingOpenSubgroup_maximalAbelianSubextension :
    fixingOpenSubgroup (maximalAbelianSubextension L) = maxAbelian (le_top : fixingOpenSubgroup L ≤ ⊤) :=
  fixingOpenSubgroup_fixedField _

/- English proof (translation)
Rewrite using `[fixingOpenSubgroup_maximalAbelianSubextension]`. Conclude with `isAbelianExtension_maxAbelian _`.
-/
theorem isAbelianExtension_fixingOpenSubgroup_maximalAbelianSubextension :
    IsAbelianExtension ⊤ (fixingOpenSubgroup (maximalAbelianSubextension L)) := by
  rw [fixingOpenSubgroup_maximalAbelianSubextension]
  exact isAbelianExtension_maxAbelian _

instance isGalois_maximalAbelianSubextension : IsGalois K (maximalAbelianSubextension L) :=
  ((isAbelianExtension_fixingOpenSubgroup_iff _).1
    (isAbelianExtension_fixingOpenSubgroup_maximalAbelianSubextension L)).1

end Dictionary

section Correspondence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

/- English proof (translation)
Rewrite using `[← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup, Subgroup.map_le_map_iff_of_injective baseUnitsEquiv.injective, (localClassFieldTheory K Ω).normGroup_le_normGroup_iff (localClassFieldTheory K Ω).classFieldAxiom ((isAbelianExtension_fixingOpenSubgroup_iff L).2 ⟨inf …`. Conclude with `fixingSubgroup_le_fixingSubgroup_iff`.
-/
theorem range_normUnits_le_range_normUnits_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsGalois K L] [IsGalois K L']
    (hL : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hL' : ∀ σ τ : L' ≃ₐ[K] L', σ * τ = τ * σ) :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup,
    Subgroup.map_le_map_iff_of_injective baseUnitsEquiv.injective,
    (localClassFieldTheory K Ω).normGroup_le_normGroup_iff (localClassFieldTheory K Ω).classFieldAxiom
      ((isAbelianExtension_fixingOpenSubgroup_iff L).2 ⟨inferInstance, hL⟩)
      ((isAbelianExtension_fixingOpenSubgroup_iff L').2 ⟨inferInstance, hL'⟩)]
  exact fixingSubgroup_le_fixingSubgroup_iff

end Correspondence

end GroundTheory.LocalField
