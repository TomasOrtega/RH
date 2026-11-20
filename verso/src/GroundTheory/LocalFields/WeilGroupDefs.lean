import Mathlib
import GroundTheory.LocalFields.MaximalUnramified
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology

section Frobenius

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/- English proof (translation)
Rewrite using `[map_zpow, unramifiedDegree_maximalUnramifiedExtensionFrobenius, ← ofAdd_zsmul, zsmul_one]`.
-/
theorem unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow (n : ℤ) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (maximalUnramifiedExtensionFrobenius K Ω ^ n) =
      Multiplicative.ofAdd (n : ℤ̂) := by
  rw [map_zpow, unramifiedDegree_maximalUnramifiedExtensionFrobenius, ← ofAdd_zsmul, zsmul_one]

/- English proof (translation)
Introduce `m n h`. Establish `h'` using `congrArg (unramifiedDegree K (maximalUnramifiedExtension K Ω)) h`. Simplify using `only [unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow] at h'`. Conclude with `Int.cast_injective (Multiplicative.ofAdd.injective h')`.
-/
theorem injective_zpow_maximalUnramifiedExtensionFrobenius :
    Function.Injective fun n : ℤ ↦ maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  intro m n h
  have h' := congrArg (unramifiedDegree K (maximalUnramifiedExtension K Ω)) h
  simp only [unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow] at h'
  exact Int.cast_injective (Multiplicative.ofAdd.injective h')

def frobeniusZPowersEquiv :
    Multiplicative ℤ ≃* Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :=
  MonoidHom.ofInjective (f := zpowersHom _ (maximalUnramifiedExtensionFrobenius K Ω))
    (fun _ _ h ↦ Multiplicative.toAdd.injective
      (injective_zpow_maximalUnramifiedExtensionFrobenius K Ω h))

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_frobeniusZPowersEquiv (n : Multiplicative ℤ) :
    (frobeniusZPowersEquiv K Ω n : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) =
      maximalUnramifiedExtensionFrobenius K Ω ^ n.toAdd :=
  rfl

end Frobenius

section Weil

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

def weilSubgroup : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω)).comap
    (AlgEquiv.restrictNormalHom (maximalUnramifiedExtension K Ω))

variable {K Ω} in

/- English proof (translation)
Simplify using `only [weilSubgroup, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]`. Conclude with `exists_congr fun n ↦ eq_comm`.
-/
theorem mem_weilSubgroup_iff {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ weilSubgroup K Ω ↔ ∃ n : ℤ,
      σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  simp only [weilSubgroup, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
  exact exists_congr fun n ↦ eq_comm

variable {K Ω} in

/- English proof (translation)
Rewrite using `[← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow K Ω n]`. Conclude with `unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm`.
-/
theorem restrictNormal_eq_frobenius_zpow_iff (σ : Ω ≃ₐ[K] Ω) (n : ℤ) :
    σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n ↔
      unramifiedDegree K Ω σ = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow K Ω n]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

variable {K Ω} in

/- English proof (translation)
Rewrite using `[mem_weilSubgroup_iff]`. Conclude with `exists_congr fun n ↦ restrictNormal_eq_frobenius_zpow_iff σ n`.
-/
theorem mem_weilSubgroup_iff_unramifiedDegree {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ weilSubgroup K Ω ↔ ∃ n : ℤ, unramifiedDegree K Ω σ = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [mem_weilSubgroup_iff]
  exact exists_congr fun n ↦ restrictNormal_eq_frobenius_zpow_iff σ n

/- English proof (translation)
Introduce `σ hσ`. Rewrite `hσ` using `[← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]`. Conclude with `mem_weilSubgroup_iff.2 ⟨0, by rw [zpow_zero]; exact hσ⟩`.
-/
theorem fixingSubgroup_le_weilSubgroup :
    (maximalUnramifiedExtension K Ω).fixingSubgroup ≤ weilSubgroup K Ω := by
  intro σ hσ
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker] at hσ
  exact mem_weilSubgroup_iff.2 ⟨0, by rw [zpow_zero]; exact hσ⟩

/- English proof (translation)
The claim follows from `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) _`.
-/
theorem exists_restrictNormal_eq_frobenius_zpow (n : ℤ) :
    ∃ σ : Ω ≃ₐ[K] Ω,
      σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) _

/- English proof (translation)
Establish `: T2Space (Ω ≃ₐ[K] Ω)` using `krullTopology_t2`. Use `set C := (weilSubgroup K Ω).topologicalClosure with hC`. Establish `hCc : IsCompact (C : Set (Ω ≃ₐ[K] Ω))` using `(Subgroup.isClosed_topologicalClosure _).isCompact`. Establish `himc : IsClosed (unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)))` using `(hCc.image continuous_unramifiedDegree).isClosed`. Establish `hsub : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) ⊆ unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω))`.

Introduce and unpack `_ ⟨n, rfl⟩`. Take `⟨σ, hσ⟩` from `exists_restrictNormal_eq_frobenius_zpow K Ω n`. Use `⟨σ, (weilSubgroup K Ω).le_topologicalClosure (mem_weilSubgroup_iff.2 ⟨n, hσ⟩), ?_⟩` and prove the remaining obligations. Use `show _ = Multiplicative.ofAdd 1 ^ n`. Rewrite using `[(restrictNormal_eq_frobenius_zpow_iff σ n).1 hσ, ← ofAdd_zsmul, zsmul_one]`.

Establish `huniv : unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) = Set.univ`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations. Rewrite using `[← dense_zpowers_ofAdd_one.closure_eq]`. Conclude with `himc.closure_subset_iff.2 hsub`. Rewrite using `[dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← hC]`.

Use `Set.eq_univ_of_forall fun τ ↦ ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hcτ⟩ : unramifiedDegree K Ω τ ∈ unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by`. Rewrite using `[huniv]`. Discharge the goal by the elementary cases of `trivial`. Establish `hk : c⁻¹ * τ ∈ (unramifiedDegree K Ω).ker`.

Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hcτ, inv_mul_cancel]`. Rewrite `hk` using `[ker_unramifiedDegree]`. Establish `hk' : c⁻¹ * τ ∈ C` using `(weilSubgroup K Ω).le_topologicalClosure (fixingSubgroup_le_weilSubgroup K Ω hk)`. Use `C.mul_mem hc hk'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem dense_weilSubgroup : Dense (weilSubgroup K Ω : Set (Ω ≃ₐ[K] Ω)) := by
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  set C := (weilSubgroup K Ω).topologicalClosure with hC
  have hCc : IsCompact (C : Set (Ω ≃ₐ[K] Ω)) := (Subgroup.isClosed_topologicalClosure _).isCompact
  have himc : IsClosed (unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω))) :=
    (hCc.image continuous_unramifiedDegree).isClosed
  have hsub : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) ⊆
      unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_restrictNormal_eq_frobenius_zpow K Ω n
    refine ⟨σ, (weilSubgroup K Ω).le_topologicalClosure (mem_weilSubgroup_iff.2 ⟨n, hσ⟩), ?_⟩
    show _ = Multiplicative.ofAdd 1 ^ n
    rw [(restrictNormal_eq_frobenius_zpow_iff σ n).1 hσ, ← ofAdd_zsmul, zsmul_one]
  have huniv : unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← dense_zpowers_ofAdd_one.closure_eq]
    exact himc.closure_subset_iff.2 hsub
  rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← hC]
  refine Set.eq_univ_of_forall fun τ ↦ ?_
  obtain ⟨c, hc, hcτ⟩ : unramifiedDegree K Ω τ ∈ unramifiedDegree K Ω '' (C : Set (Ω ≃ₐ[K] Ω)) := by
    rw [huniv]; trivial
  have hk : c⁻¹ * τ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcτ, inv_mul_cancel]
  rw [ker_unramifiedDegree] at hk
  have hk' : c⁻¹ * τ ∈ C :=
    (weilSubgroup K Ω).le_topologicalClosure (fixingSubgroup_le_weilSubgroup K Ω hk)
  have := C.mul_mem hc hk'
  rwa [mul_inv_cancel_left] at this

def WeilGroup : Type _ := weilSubgroup K Ω

namespace WeilGroup

instance : Group (WeilGroup K Ω) := inferInstanceAs (Group (weilSubgroup K Ω))

def toGal : WeilGroup K Ω →* (Ω ≃ₐ[K] Ω) := (weilSubgroup K Ω).subtype

/- English proof (translation)
The claim follows from `Subtype.val_injective`.
-/
theorem toGal_injective : Function.Injective (toGal K Ω) := Subtype.val_injective

/- English proof (translation)
The claim follows from `Subgroup.range_subtype _`.
-/
theorem range_toGal : (toGal K Ω).range = weilSubgroup K Ω := Subgroup.range_subtype _

variable {K Ω} in
/- English proof (translation)
The claim follows from `σ.2`.
-/
theorem toGal_mem (σ : WeilGroup K Ω) : toGal K Ω σ ∈ weilSubgroup K Ω := σ.2

variable {K Ω} in

def mk (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ weilSubgroup K Ω) : WeilGroup K Ω := ⟨σ, hσ⟩

variable {K Ω} in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toGal_mk (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ weilSubgroup K Ω) : toGal K Ω (mk σ hσ) = σ := rfl

variable {K Ω} in
@[ext]
/- English proof (translation)
The claim follows from `toGal_injective K Ω h`.
-/
theorem ext {σ τ : WeilGroup K Ω} (h : toGal K Ω σ = toGal K Ω τ) : σ = τ := toGal_injective K Ω h

def restrictFrobenius : WeilGroup K Ω →* Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :=
  ((AlgEquiv.restrictNormalHom (maximalUnramifiedExtension K Ω)).comp (toGal K Ω)).codRestrict _
    fun σ ↦ σ.2

def degree : WeilGroup K Ω →* Multiplicative ℤ :=
  (frobeniusZPowersEquiv K Ω).symm.toMonoidHom.comp (restrictFrobenius K Ω)

variable {K Ω}

/- English proof (translation)
Establish `h` using `(frobeniusZPowersEquiv K Ω).apply_symm_apply (restrictFrobenius K Ω σ)`. Establish `h'` using `congrArg Subtype.val h`. Rewrite `h'` using `[coe_frobeniusZPowersEquiv]`. Conclude with `h'.symm`.
-/
theorem restrictNormal_toGal (σ : WeilGroup K Ω) :
    (toGal K Ω σ).restrictNormal (maximalUnramifiedExtension K Ω) =
      maximalUnramifiedExtensionFrobenius K Ω ^ (degree K Ω σ).toAdd := by
  have h := (frobeniusZPowersEquiv K Ω).apply_symm_apply (restrictFrobenius K Ω σ)
  have h' := congrArg Subtype.val h
  rw [coe_frobeniusZPowersEquiv] at h'
  exact h'.symm

/- English proof (translation)
Rewrite using `[restrictNormal_toGal]`. Conclude with `⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦ Multiplicative.toAdd.injective (injective_zpow_maximalUnramifiedExtensionFrobenius K Ω h)⟩`.
-/
theorem degree_eq_iff (σ : WeilGroup K Ω) (n : ℤ) :
    degree K Ω σ = Multiplicative.ofAdd n ↔
      (toGal K Ω σ).restrictNormal (maximalUnramifiedExtension K Ω) =
        maximalUnramifiedExtensionFrobenius K Ω ^ n := by
  rw [restrictNormal_toGal]
  exact ⟨fun h ↦ by rw [h, toAdd_ofAdd], fun h ↦
    Multiplicative.toAdd.injective (injective_zpow_maximalUnramifiedExtensionFrobenius K Ω h)⟩

/- English proof (translation)
The claim follows from `(restrictNormal_eq_frobenius_zpow_iff _ _).1 (restrictNormal_toGal σ)`.
-/
theorem unramifiedDegree_toGal (σ : WeilGroup K Ω) :
    unramifiedDegree K Ω (toGal K Ω σ) = Multiplicative.ofAdd (((degree K Ω σ).toAdd : ℤ) : ℤ̂) :=
  (restrictNormal_eq_frobenius_zpow_iff _ _).1 (restrictNormal_toGal σ)

/- English proof (translation)
Rewrite using `[degree_eq_iff, restrictNormal_eq_frobenius_zpow_iff]`.
-/
theorem degree_eq_iff_unramifiedDegree (σ : WeilGroup K Ω) (n : ℤ) :
    degree K Ω σ = Multiplicative.ofAdd n ↔
      unramifiedDegree K Ω (toGal K Ω σ) = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [degree_eq_iff, restrictNormal_eq_frobenius_zpow_iff]

/- English proof (translation)
Introduce `n`. Take `⟨σ, hσ⟩` from `exists_restrictNormal_eq_frobenius_zpow K Ω n.toAdd`. Conclude with `⟨mk σ (mem_weilSubgroup_iff.2 ⟨_, hσ⟩), (degree_eq_iff _ n.toAdd).2 hσ⟩`.
-/
theorem degree_surjective : Function.Surjective (degree K Ω) := by
  intro n
  obtain ⟨σ, hσ⟩ := exists_restrictNormal_eq_frobenius_zpow K Ω n.toAdd
  exact ⟨mk σ (mem_weilSubgroup_iff.2 ⟨_, hσ⟩), (degree_eq_iff _ n.toAdd).2 hσ⟩

variable (K Ω) in

def inertia : Subgroup (WeilGroup K Ω) := (degree K Ω).ker

/- English proof (translation)
Rewrite using `[inertia, MonoidHom.mem_ker, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, ← ofAdd_zero, degree_eq_iff, zpow_zero]`.
-/
theorem mem_inertia_iff {σ : WeilGroup K Ω} :
    σ ∈ inertia K Ω ↔ toGal K Ω σ ∈ (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  rw [inertia, MonoidHom.mem_ker, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker,
    AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, ← ofAdd_zero, degree_eq_iff, zpow_zero]

variable (K Ω) in

/- English proof (translation)
Use extensionality with `σ`. Conclude with `mem_inertia_iff`.
-/
theorem inertia_eq_comap :
    inertia K Ω = (maximalUnramifiedExtension K Ω).fixingSubgroup.comap (toGal K Ω) := by
  ext σ
  exact mem_inertia_iff

variable (K Ω) in

/- English proof (translation)
Use `⟨rfl, degree_surjective, ?_⟩` and prove the remaining obligations. Rewrite using `[inertia_eq_comap, Subgroup.map_comap_eq, range_toGal]`. Conclude with `inf_of_le_right (fixingSubgroup_le_weilSubgroup K Ω)`.
-/
theorem exact_inertia_degree :
    (degree K Ω).ker = inertia K Ω ∧ Function.Surjective (degree K Ω) ∧
      (inertia K Ω).map (toGal K Ω) = (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  refine ⟨rfl, degree_surjective, ?_⟩
  rw [inertia_eq_comap, Subgroup.map_comap_eq, range_toGal]
  exact inf_of_le_right (fixingSubgroup_le_weilSubgroup K Ω)

variable (K Ω) in

def toGalProd : WeilGroup K Ω →* (Ω ≃ₐ[K] Ω) × Multiplicative ℤ := (toGal K Ω).prod (degree K Ω)

variable (K Ω) in

instance instTopologicalSpace : TopologicalSpace (WeilGroup K Ω) :=
  TopologicalSpace.induced (toGalProd K Ω) inferInstance

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isInducing_toGalProd : IsInducing (toGalProd K Ω) := ⟨rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨isInducing_toGalProd, fun _ _ h ↦ toGal_injective K Ω (congrArg Prod.fst h)⟩`.
-/
theorem isEmbedding_toGalProd : IsEmbedding (toGalProd K Ω) :=
  ⟨isInducing_toGalProd, fun _ _ h ↦ toGal_injective K Ω (congrArg Prod.fst h)⟩

instance : IsTopologicalGroup (WeilGroup K Ω) :=
  isInducing_toGalProd.topologicalGroup (toGalProd K Ω)

instance : T2Space (WeilGroup K Ω) :=
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  isEmbedding_toGalProd.t2Space

/- English proof (translation)
The claim follows from `continuous_fst.comp isInducing_toGalProd.continuous`.
-/
theorem continuous_toGal : Continuous (toGal K Ω) :=
  continuous_fst.comp isInducing_toGalProd.continuous

/- English proof (translation)
The claim follows from `continuous_snd.comp isInducing_toGalProd.continuous`.
-/
theorem continuous_degree : Continuous (degree K Ω) :=
  continuous_snd.comp isInducing_toGalProd.continuous

/- English proof (translation)
Rewrite using `[isInducing_toGalProd.continuous_iff, continuous_prodMk]`. Both sides reduce to the same expression.
-/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → WeilGroup K Ω} :
    Continuous f ↔ Continuous (toGal K Ω ∘ f) ∧ Continuous (degree K Ω ∘ f) := by
  rw [isInducing_toGalProd.continuous_iff, continuous_prodMk]
  rfl

/- English proof (translation)
The claim follows from `(isOpen_discrete ({1} : Set (Multiplicative ℤ))).preimage continuous_degree`.
-/
theorem isOpen_inertia : IsOpen (inertia K Ω : Set (WeilGroup K Ω)) :=
  (isOpen_discrete ({1} : Set (Multiplicative ℤ))).preimage continuous_degree

/- English proof (translation)
The claim follows from `OpenSubgroup.isClosed ⟨inertia K Ω, isOpen_inertia⟩`.
-/
theorem isClosed_inertia : IsClosed (inertia K Ω : Set (WeilGroup K Ω)) :=
  OpenSubgroup.isClosed ⟨inertia K Ω, isOpen_inertia⟩

variable (K Ω) in

def inertiaEquiv : inertia K Ω ≃ₜ* (maximalUnramifiedExtension K Ω).fixingSubgroup where
  toFun σ := ⟨toGal K Ω σ, mem_inertia_iff.1 σ.2⟩
  invFun τ := ⟨mk τ (fixingSubgroup_le_weilSubgroup K Ω τ.2), mem_inertia_iff.2 τ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_toGal.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hc : Continuous fun τ : (maximalUnramifiedExtension K Ω).fixingSubgroup ↦
        mk (τ : Ω ≃ₐ[K] Ω) (fixingSubgroup_le_weilSubgroup K Ω τ.2) := by
      refine (continuous_iff (K := K) (Ω := Ω)).2 ⟨continuous_subtype_val, ?_⟩
      have : (degree K Ω ∘ fun τ : (maximalUnramifiedExtension K Ω).fixingSubgroup ↦
          mk (τ : Ω ≃ₐ[K] Ω) (fixingSubgroup_le_weilSubgroup K Ω τ.2)) = fun _ ↦ 1 :=
        funext fun τ ↦ (mem_inertia_iff (σ := mk _ (fixingSubgroup_le_weilSubgroup K Ω τ.2))).2 τ.2
      rw [this]
      exact continuous_const
    exact hc.subtype_mk _

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_inertiaEquiv_apply (σ : inertia K Ω) :
    ((inertiaEquiv K Ω σ : (maximalUnramifiedExtension K Ω).fixingSubgroup) : Ω ≃ₐ[K] Ω) =
      toGal K Ω σ :=
  rfl

instance : CompactSpace (inertia K Ω) :=
  have : CompactSpace (maximalUnramifiedExtension K Ω).fixingSubgroup :=
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed (k := K) (K := Ω) (maximalUnramifiedExtension K Ω)).isCompact
  (inertiaEquiv K Ω).toHomeomorph.symm.compactSpace

/- English proof (translation)
The claim follows from `isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (inertia K Ω)))`.
-/
theorem isCompact_inertia : IsCompact (inertia K Ω : Set (WeilGroup K Ω)) :=
  isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (inertia K Ω)))

instance : LocallyCompactSpace (WeilGroup K Ω) :=
  isCompact_inertia.locallyCompactSpace_of_mem_nhds_of_group
    (isOpen_inertia.mem_nhds (Subgroup.one_mem _))

/- English proof (translation)
Establish `h` using `dense_weilSubgroup K Ω`. Rewrite `h` using `[← range_toGal, MonoidHom.coe_range]`. Conclude with `h`.
-/
theorem denseRange_toGal : DenseRange (toGal K Ω) := by
  have h := dense_weilSubgroup K Ω
  rw [← range_toGal, MonoidHom.coe_range] at h
  exact h

/- English proof (translation)
The claim follows from `hU.preimage continuous_toGal`.
-/
theorem isOpen_preimage_toGal {U : Set (Ω ≃ₐ[K] Ω)} (hU : IsOpen U) :
    IsOpen (toGal K Ω ⁻¹' U) :=
  hU.preimage continuous_toGal

/- English proof (translation)
The claim follows from `degree_surjective _`.
-/
theorem exists_degree_eq_one : ∃ φ : WeilGroup K Ω, degree K Ω φ = Multiplicative.ofAdd 1 :=
  degree_surjective _

end WeilGroup

end Weil

end GroundTheory.LocalField
