import Mathlib
import GroundTheory.GlobalFields.ExistenceTheorem.Kummer
import GroundTheory.GlobalFields.ExistenceTheorem.NormLimitation
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup

noncomputable section

universe u

instance numberField_of_finiteDimensional {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L] : NumberField L :=
  NumberField.of_module_finite K L

section NormGroup

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Use extensionality with `c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, rfl⟩`. Take `⟨e, rfl⟩` from `(ideleClassEquiv (τ : L ≃+* L')).surjective d`. Conclude with `⟨e, (ideleClassNorm_ideleClassEquiv τ e).symm⟩`.

Introduce and unpack `⟨d, rfl⟩`. Conclude with `⟨_, ideleClassNorm_ideleClassEquiv τ d⟩`.
-/
theorem range_ideleClassNorm_congr {L L' : Type*} [Field L] [NumberField L] [Field L']
    [NumberField L'] [Algebra K L] [Algebra K L'] (τ : L ≃ₐ[K] L') :
    (ideleClassNorm K L').range = (ideleClassNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨e, rfl⟩ := (ideleClassEquiv (τ : L ≃+* L')).surjective d
    exact ⟨e, (ideleClassNorm_ideleClassEquiv τ e).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨_, ideleClassNorm_ideleClassEquiv τ d⟩

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]

/- English proof (translation)
Use extensionality with `c`. Rewrite using `[← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField, AlgEquiv.restrictNormal_eq_one_iff, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]`.
-/
theorem range_ideleClassNorm_eq_comap (F : IntermediateField K M) :
    (ideleClassNorm K F).range = F.fixingSubgroup.comap (reciprocityMap K M) := by
  ext c
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField,
    AlgEquiv.restrictNormal_eq_one_iff, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]

end NormGroup

section Compositum

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/- English proof (translation)
Establish `h₁ : L₁ ≤ L₁ ⊔ L₂` using `le_sup_left`. Establish `h₂ : L₂ ≤ L₁ ⊔ L₂` using `le_sup_right`. Establish `key : ∀ (L : IntermediateField K Ω) [IsAbelianGalois K L] (h : L ≤ L₁ ⊔ L₂) (σ τ : Gal(↥(L₁ ⊔ L₂)/K)), (τ * σ)⁻¹ * (σ * τ) ∈ (restrict h).fixingSubgroup`. Introduce `L _ h σ τ`. Set `_ : Algebra L ↥(L₁ ⊔ L₂)` to `(IntermediateField.inclusion h).toAlgebra`.

Establish `: IsScalarTower K L ↥(L₁ ⊔ L₂)` using `IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Take `⟨x, rfl⟩ : ∃ x : L, algebraMap L ↥(L₁ ⊔ L₂) x = y` from `⟨⟨y, (mem_restrict h y).1 hy⟩, rfl⟩`. Establish `hm : AlgEquiv.restrictNormalHom (F` using `K) (K₁ := ↥(L₁ ⊔ L₂)) L ((τ * σ)⁻¹ * (σ * τ)) = 1 := by`.

Rewrite using `[map_mul, map_inv, map_mul, map_mul, mul_comm' (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L τ), inv_mul_cancel]`. Establish `hc` using `AlgEquiv.restrictNormal_commutes ((τ * σ)⁻¹ * (σ * τ)) L x`. Express the relevant statement in the definitionally equal form `algebraMap L _ (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L ((τ * σ)⁻¹ * (σ * τ)) x) = _ at hc`. Rewrite `hc` using `[hm, AlgEquiv.one_apply]`. Conclude with `hc.symm`.

Use `⟨⟨fun σ τ ↦ ?_⟩⟩` and prove the remaining obligations. Establish `htop : restrict h₁ ⊔ restrict h₂ = (⊤ : IntermediateField K ↥(L₁ ⊔ L₂))`. Use `top_unique fun y _ ↦ ?_` and prove the remaining obligations. Establish `hy : (y : Ω) ∈ lift (restrict h₁) ⊔ lift (restrict h₂)`. Rewrite using `[lift_restrict, lift_restrict]`.

Conclude with `y.2`. Rewrite `hy` using `[← lift_sup]`. Conclude with `(mem_lift y).1 hy`. Establish `hρ : (τ * σ)⁻¹ * (σ * τ) ∈ (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)).fixingSubgroup`. Rewrite using `[← htop, fixingSubgroup_sup]`.

Conclude with `⟨key L₁ h₁ σ τ, key L₂ h₂ σ τ⟩`. Establish `h1 : (τ * σ)⁻¹ * (σ * τ) = 1` using `AlgEquiv.ext fun y ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ y mem_top`. Rewrite `h1` using `[inv_mul_eq_one]`. Conclude with `h1.symm`.
-/
theorem isMulCommutative_sup (L₁ L₂ : IntermediateField K Ω) [IsAbelianGalois K L₁]
    [IsAbelianGalois K L₂] [Normal K ↥(L₁ ⊔ L₂)] : IsMulCommutative Gal(↥(L₁ ⊔ L₂)/K) := by
  have h₁ : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
  have h₂ : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
  have key : ∀ (L : IntermediateField K Ω) [IsAbelianGalois K L] (h : L ≤ L₁ ⊔ L₂)
      (σ τ : Gal(↥(L₁ ⊔ L₂)/K)), (τ * σ)⁻¹ * (σ * τ) ∈ (restrict h).fixingSubgroup := by
    intro L _ h σ τ
    let _ : Algebra L ↥(L₁ ⊔ L₂) := (IntermediateField.inclusion h).toAlgebra
    have : IsScalarTower K L ↥(L₁ ⊔ L₂) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨x, rfl⟩ : ∃ x : L, algebraMap L ↥(L₁ ⊔ L₂) x = y := ⟨⟨y, (mem_restrict h y).1 hy⟩, rfl⟩
    have hm : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L ((τ * σ)⁻¹ * (σ * τ)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm' (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L τ), inv_mul_cancel]
    have hc := AlgEquiv.restrictNormal_commutes ((τ * σ)⁻¹ * (σ * τ)) L x
    change algebraMap L _ (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L
      ((τ * σ)⁻¹ * (σ * τ)) x) = _ at hc
    rw [hm, AlgEquiv.one_apply] at hc
    exact hc.symm
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  have htop : restrict h₁ ⊔ restrict h₂ = (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)) := by
    refine top_unique fun y _ ↦ ?_
    have hy : (y : Ω) ∈ lift (restrict h₁) ⊔ lift (restrict h₂) := by
      rw [lift_restrict, lift_restrict]
      exact y.2
    rw [← lift_sup] at hy
    exact (mem_lift y).1 hy
  have hρ : (τ * σ)⁻¹ * (σ * τ) ∈ (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)).fixingSubgroup := by
    rw [← htop, fixingSubgroup_sup]
    exact ⟨key L₁ h₁ σ τ, key L₂ h₂ σ τ⟩
  have h1 : (τ * σ)⁻¹ * (σ * τ) = 1 :=
    AlgEquiv.ext fun y ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ y mem_top
  rw [inv_mul_eq_one] at h1
  exact h1.symm

instance isAbelianGalois_sup [CharZero K] (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    IsAbelianGalois K ↥(L₁ ⊔ L₂) :=
  have : IsGalois K ↥(L₁ ⊔ L₂) := ⟨⟩
  { toIsMulCommutative := isMulCommutative_sup L₁ L₂ }

end Compositum

section Existence

variable {K : Type u} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨E, _, _, _, _, hE⟩` from `exists_isAbelianGalois_range_ideleClassNorm_le (K := K) L`. Conclude with `⟨fixedField (N.map (reciprocityMap K E)), inferInstance, inferInstance, inferInstance, inferInstance, range_ideleClassNorm_fixedField N (hE.trans hN)⟩`.
-/
theorem exists_isAbelianGalois_range_ideleClassNorm_eq_of_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] (N : Subgroup (IdeleClassGroup K)) (hN : (ideleClassNorm K L).range ≤ N) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range = N := by
  obtain ⟨E, _, _, _, _, hE⟩ := exists_isAbelianGalois_range_ideleClassNorm_le (K := K) L
  exact ⟨fixedField (N.map (reciprocityMap K E)), inferInstance, inferInstance, inferInstance,
    inferInstance, range_ideleClassNorm_fixedField N (hE.trans hN)⟩

/- English proof (translation)
Establish `: NeZero N.index` using `⟨Subgroup.FiniteIndex.index_ne_zero⟩`. Set `K'` to `CyclotomicField N.index K`. Establish `: HasEnoughRootsOfUnity K' N.index` using `⟨⟨_, IsCyclotomicExtension.zeta_spec N.index K K'⟩, rootsOfUnity.isCyclic _ _⟩`. Set `N'` to `N.comap (ideleClassNorm K K')`. Establish `hN' : IsOpen (N' : Set (IdeleClassGroup K'))` using `hN.preimage continuous_ideleClassNorm`.

Establish `: N.Normal` using `⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩`. Establish `hpow : ∀ c, c ^ N.index ∈ N'` using `fun c ↦ by`. Rewrite using `[Subgroup.mem_comap, map_pow]`. Conclude with `N.pow_index_mem _`. Take `⟨L', _, _, _, -, -, hL'⟩` from `exists_isAbelianGalois_range_ideleClassNorm_eq N' hN' hpow`.

Set `_ : Algebra K L'` to `((algebraMap K' L').comp (algebraMap K K')).toAlgebra`. Establish `: IsScalarTower K K' L'` using `IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`. Use `exists_isAbelianGalois_range_ideleClassNorm_eq_of_le L' N ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[← ideleClassNorm_ideleClassNorm (L := K')]`.

Establish `hc : ideleClassNorm K' L' c ∈ N'` using `hL' ▸ ⟨c, rfl⟩`. Conclude with `hc`.
-/
theorem exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex
    (N : Subgroup (IdeleClassGroup K)) (hN : IsOpen (N : Set (IdeleClassGroup K))) [N.FiniteIndex] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsAbelianGalois K L ∧ (ideleClassNorm K L).range = N := by
  have : NeZero N.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  let K' := CyclotomicField N.index K
  have : HasEnoughRootsOfUnity K' N.index :=
    ⟨⟨_, IsCyclotomicExtension.zeta_spec N.index K K'⟩, rootsOfUnity.isCyclic _ _⟩
  let N' := N.comap (ideleClassNorm K K')
  have hN' : IsOpen (N' : Set (IdeleClassGroup K')) := hN.preimage continuous_ideleClassNorm
  have : N.Normal := ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  have hpow : ∀ c, c ^ N.index ∈ N' := fun c ↦ by
    rw [Subgroup.mem_comap, map_pow]
    exact N.pow_index_mem _
  obtain ⟨L', _, _, _, -, -, hL'⟩ := exists_isAbelianGalois_range_ideleClassNorm_eq N' hN' hpow
  let _ : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine exists_isAbelianGalois_range_ideleClassNorm_eq_of_le L' N ?_
  rintro _ ⟨c, rfl⟩
  rw [← ideleClassNorm_ideleClassNorm (L := K')]
  have hc : ideleClassNorm K' L' c ∈ N' := hL' ▸ ⟨c, rfl⟩
  exact hc

end Existence

section Open

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

/- English proof (translation)
Rewrite using `[← ker_reciprocityMap, MonoidHom.coe_ker]`. Conclude with `(isOpen_discrete {1}).preimage continuous_reciprocityMap`.
-/
theorem isOpen_range_ideleClassNorm :
    IsOpen ((ideleClassNorm K L).range : Set (IdeleClassGroup K)) := by
  rw [← ker_reciprocityMap, MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage continuous_reciprocityMap

instance finiteIndex_range_ideleClassNorm : (ideleClassNorm K L).range.FiniteIndex :=
  ⟨by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'⟩

end Open

section Correspondence

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h₁ : L₁ ≤ L₁ ⊔ L₂` using `le_sup_left`. Establish `h₂ : L₂ ≤ L₁ ⊔ L₂` using `le_sup_right`. Establish `e₁ : (ideleClassNorm K (restrict h₁)).range = (ideleClassNorm K L₁).range` using `range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₁))`.

Establish `e₂ : (ideleClassNorm K (restrict h₂)).range = (ideleClassNorm K L₂).range` using `range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₂))`. Rewrite `h` using `[← e₁, ← e₂, range_ideleClassNorm_eq_comap, range_ideleClassNorm_eq_comap, Subgroup.comap_le_comap_of_surjective reciprocityMap_surjective]`. Establish `hF : restrict h₁ ≤ restrict h₂`. Rewrite using `[← IsGalois.intermediateFieldEquivSubgroup.le_iff_le]`. Conclude with `h`.

Introduce `x hx`. Conclude with `(mem_restrict h₂ ⟨x, h₁ hx⟩).1 (hF ((mem_restrict h₁ ⟨x, h₁ hx⟩).2 hx))`. Introduce `h`. Set `_ : Algebra L₁ L₂` to `(IntermediateField.inclusion h).toAlgebra`. Establish `: IsScalarTower K L₁ L₂` using `IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`.

Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `⟨ideleClassNorm L₁ L₂ c, ideleClassNorm_ideleClassNorm c⟩`.
-/
theorem range_ideleClassNorm_le_range_iff (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    (ideleClassNorm K L₂).range ≤ (ideleClassNorm K L₁).range ↔ L₁ ≤ L₂ := by
  constructor
  · intro h
    have h₁ : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
    have h₂ : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
    have e₁ : (ideleClassNorm K (restrict h₁)).range = (ideleClassNorm K L₁).range :=
      range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₁))
    have e₂ : (ideleClassNorm K (restrict h₂)).range = (ideleClassNorm K L₂).range :=
      range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₂))
    rw [← e₁, ← e₂, range_ideleClassNorm_eq_comap, range_ideleClassNorm_eq_comap,
      Subgroup.comap_le_comap_of_surjective reciprocityMap_surjective] at h
    have hF : restrict h₁ ≤ restrict h₂ := by
      rw [← IsGalois.intermediateFieldEquivSubgroup.le_iff_le]
      exact h
    intro x hx
    exact (mem_restrict h₂ ⟨x, h₁ hx⟩).1 (hF ((mem_restrict h₁ ⟨x, h₁ hx⟩).2 hx))
  · intro h
    let _ : Algebra L₁ L₂ := (IntermediateField.inclusion h).toAlgebra
    have : IsScalarTower K L₁ L₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm L₁ L₂ c, ideleClassNorm_ideleClassNorm c⟩

variable [IsAlgClosed Ω]

/- English proof (translation)
Take `⟨L, _, _, _, _, hL⟩` from `exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex N hN`. Set `f : L →ₐ[K] Ω` to `IsAlgClosed.lift`. Set `τ` to `AlgEquiv.ofInjectiveField f`. Establish `: FiniteDimensional K f.fieldRange` using `LinearEquiv.finiteDimensional τ.toLinearEquiv`. Establish `: IsAbelianGalois K f.fieldRange` using `IsAbelianGalois.of_algHom τ.symm.toAlgHom`.

Conclude with `⟨f.fieldRange, inferInstance, inferInstance, (range_ideleClassNorm_congr τ).trans hL⟩`.
-/
theorem exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex
    (N : Subgroup (IdeleClassGroup K)) (hN : IsOpen (N : Set (IdeleClassGroup K))) [N.FiniteIndex] :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      (ideleClassNorm K L).range = N := by
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex N hN
  let f : L →ₐ[K] Ω := IsAlgClosed.lift
  let τ := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := LinearEquiv.finiteDimensional τ.toLinearEquiv
  have : IsAbelianGalois K f.fieldRange := IsAbelianGalois.of_algHom τ.symm.toAlgHom
  exact ⟨f.fieldRange, inferInstance, inferInstance, (range_ideleClassNorm_congr τ).trans hL⟩

variable (K Ω) in

abbrev FiniteAbelianSubfield : Type u :=
  {L : IntermediateField K Ω // FiniteDimensional K L ∧ IsAbelianGalois K L}

variable (K) in

abbrev OpenFiniteIndexSubgroup : Type u :=
  {N : Subgroup (IdeleClassGroup K) // IsOpen (N : Set (IdeleClassGroup K)) ∧ N.FiniteIndex}

def normGroup (L : FiniteAbelianSubfield K Ω) : OpenFiniteIndexSubgroup K :=
  haveI := L.2.1
  haveI := L.2.2
  ⟨(ideleClassNorm K L.1).range, isOpen_range_ideleClassNorm, inferInstance⟩

/- English proof (translation)
Use `L₁.2.1` as an intermediate fact. Use `L₁.2.2` as an intermediate fact. Use `L₂.2.1` as an intermediate fact. Use `L₂.2.2` as an intermediate fact. Conclude with `range_ideleClassNorm_le_range_iff L₁.1 L₂.1`.
-/
theorem normGroup_le_normGroup_iff (L₁ L₂ : FiniteAbelianSubfield K Ω) :
    normGroup L₂ ≤ normGroup L₁ ↔ L₁ ≤ L₂ := by
  have := L₁.2.1
  have := L₁.2.2
  have := L₂.2.1
  have := L₂.2.2
  exact range_ideleClassNorm_le_range_iff L₁.1 L₂.1

/- English proof (translation)
The claim follows from `fun L₁ L₂ h ↦ le_antisymm ((normGroup_le_normGroup_iff L₁ L₂).1 h.ge) ((normGroup_le_normGroup_iff L₂ L₁).1 h.le)`.
-/
theorem normGroup_injective : Function.Injective (normGroup (K := K) (Ω := Ω)) := fun L₁ L₂ h ↦
  le_antisymm ((normGroup_le_normGroup_iff L₁ L₂).1 h.ge) ((normGroup_le_normGroup_iff L₂ L₁).1 h.le)

/- English proof (translation)
The claim follows from `fun N ↦ by have := N.2.2 obtain ⟨L, h1, h2, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω) N.1 N.2.1 exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩`.
-/
theorem normGroup_surjective : Function.Surjective (normGroup (K := K) (Ω := Ω)) := fun N ↦ by
  have := N.2.2
  obtain ⟨L, h1, h2, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω)
    N.1 N.2.1
  exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩

variable (K Ω) in

def normGroupOrderIso : FiniteAbelianSubfield K Ω ≃o (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := (Equiv.ofBijective normGroup ⟨normGroup_injective, normGroup_surjective⟩).trans
    OrderDual.toDual
  map_rel_iff' {L₁ L₂} := normGroup_le_normGroup_iff L₁ L₂

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normGroupOrderIso_apply (L : FiniteAbelianSubfield K Ω) :
    OrderDual.ofDual (normGroupOrderIso K Ω L) = normGroup L :=
  rfl

end Correspondence

end

end GroundTheory.Global
