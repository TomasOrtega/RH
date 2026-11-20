import Mathlib
import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
import GroundTheory.GlobalFields.IdeleClassGroup.ConjugateNorm

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

def ideleClassNorm {F E : FiniteSubfield} (h : F ≤ E) :
    IdeleClassGroup E.1 →* IdeleClassGroup F.1 :=
  letI := algebraOfLE h
  GroundTheory.Global.ideleClassNorm F.1 E.1

def galoisClosure (F : FiniteSubfield) : FiniteSubfield :=
  ⟨normalClosure ℚ F.1 ℚ̄, inferInstance⟩

/- English proof (translation)
The claim follows from `show F.1 ≤ normalClosure ℚ F.1 ℚ̄ from IntermediateField.le_normalClosure F.1`.
-/
theorem le_galoisClosure (F : FiniteSubfield) : F ≤ galoisClosure F :=
  show F.1 ≤ normalClosure ℚ F.1 ℚ̄ from IntermediateField.le_normalClosure F.1

instance (F : FiniteSubfield) : IsGalois ℚ (galoisClosure F).1 :=
  IsGalois.normalClosure ℚ F.1 ℚ̄

/- English proof (translation)
The claim follows from `(IntermediateField.finrank_eq_fixingSubgroup_index (E' := ℚ̄) F.1).symm`.
-/
theorem index_fixingSubgroup (F : FiniteSubfield) :
    F.1.fixingSubgroup.index = Module.finrank ℚ F.1 :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (E' := ℚ̄) F.1).symm

instance (F : FiniteSubfield) : F.1.fixingSubgroup.FiniteIndex :=
  ⟨by rw [index_fixingSubgroup]; exact Module.finrank_pos.ne'⟩

/- English proof (translation)
Set `` to `algebraOfLE h`. Establish `: IsScalarTower ℚ F.1 E.1` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Establish `: Module.Free F.1 E.1` using `Module.Free.of_divisionRing _ _`. Establish `: FiniteDimensional F.1 E.1` using `FiniteDimensional.right ℚ F.1 E.1`. Establish `h1` using `Subgroup.relIndex_mul_index (IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h))`.

Rewrite `h1` using `[index_fixingSubgroup, index_fixingSubgroup, ← Module.finrank_mul_finrank ℚ F.1 E.1, mul_comm (Module.finrank ℚ F.1)]`. Conclude with `Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1`.
-/
theorem relIndex_fixingSubgroup {F E : FiniteSubfield} (h : F ≤ E) :
    letI := algebraOfLE h
    E.1.fixingSubgroup.relIndex F.1.fixingSubgroup = Module.finrank F.1 E.1 := by
  let := algebraOfLE h
  have : IsScalarTower ℚ F.1 E.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Free F.1 E.1 := Module.Free.of_divisionRing _ _
  have : FiniteDimensional F.1 E.1 := FiniteDimensional.right ℚ F.1 E.1
  have h1 := Subgroup.relIndex_mul_index
    (IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h))
  rw [index_fixingSubgroup, index_fixingSubgroup, ← Module.finrank_mul_finrank ℚ F.1 E.1,
    mul_comm (Module.finrank ℚ F.1)] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

/- English proof (translation)
The claim follows from `InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩`.
-/
theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    (fixedField (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩

def ofOpenSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) : FiniteSubfield :=
  ⟨fixedField (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)), (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)⟩

/- English proof (translation)
The claim follows from `fixingSubgroup_fixedField_openSubgroup U`.
-/
theorem fixingSubgroup_ofOpenSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    (ofOpenSubgroup U).1.fixingSubgroup = U :=
  fixingSubgroup_fixedField_openSubgroup U

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield

/- English proof (translation)
The claim follows from `(smul_of σ M c).trans (of_ideleClassEquiv_congr _ _ h c)`.
-/
theorem smul_of_eq_of_ideleClassEquiv {M : FiniteSubfield} (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ : M.1 ≃+* M.1)
    (h : ∀ x : M.1, σ x = τ x) (c : IdeleClassGroup M.1) :
    σ • of M c = of M (ideleClassEquiv τ c) :=
  (smul_of σ M c).trans (of_ideleClassEquiv_congr _ _ h c)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Take `⟨E, c, rfl⟩` from `exists_of z`. Set `S : FiniteSubfield` to `⟨F.1 ⊔ E.1, inferInstance⟩`. Set `M` to `galoisClosure S`.

Establish `hFM : F ≤ M` using `le_trans (show F.1 ≤ F.1 ⊔ E.1 from le_sup_left) (le_galoisClosure S)`. Establish `hEM : E ≤ M` using `le_trans (show E.1 ≤ F.1 ⊔ E.1 from le_sup_right) (le_galoisClosure S)`. Rewrite `hz`, the goal using `[← of_ideleClassMap hEM c]`. Set `` to `algebraOfLE hFM`. Establish `: IsScalarTower ℚ F.1 M.1` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`.

Establish `: IsGalois F.1 M.1` using `IsGalois.tower_top_of_isGalois ℚ F.1 M.1`. Establish `hfix : ∀ σ : M.1 ≃ₐ[F.1] M.1, σ • FiniteSubfield.ideleClassMap hEM c = FiniteSubfield.ideleClassMap hEM c`. Introduce `σ`. Set `σ' : ℚ̄ ≃ₐ[ℚ] ℚ̄` to `(σ.restrictScalars ℚ).liftNormal ℚ̄`. Establish `hσ' : ∀ x : M.1, σ' x = σ x` using `fun x ↦ (σ.restrictScalars ℚ).liftNormal_commutes ℚ̄ x`.

Establish `hmem : σ' ∈ F.1.fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `h1` using `hσ' (algebraMap F.1 M.1 ⟨x, hx⟩)`. Rewrite `h1` using `[σ.commutes]`.

Conclude with `h1`. Establish `h1` using `hz σ' hmem`. Rewrite `h1` using `[smul_of_eq_of_ideleClassEquiv σ' (σ : M.1 ≃+* M.1) hσ']`. Conclude with `of_injective M h1`. Take `⟨d, hd⟩` from `(forall_smul_eq_iff_mem_range_ideleClassMap (K := F.1) (FiniteSubfield.ideleClassMap hEM c)).1 hfix`.

Conclude with `⟨d, by rw [← hd]; exact (of_ideleClassMap hFM d).symm⟩`. Introduce and unpack `_ ⟨c, rfl⟩ σ hσ`. Conclude with `smul_of_eq_of_mem_fixingSubgroup hσ c`.
-/
theorem fixedModule_fixingSubgroup (F : FiniteSubfield) :
    fixedModule IdeleClassLimit F.1.fixingSubgroup = (of F).range := by
  apply le_antisymm
  · intro z hz
    obtain ⟨E, c, rfl⟩ := exists_of z
    let S : FiniteSubfield := ⟨F.1 ⊔ E.1, inferInstance⟩
    let M := galoisClosure S
    have hFM : F ≤ M := le_trans (show F.1 ≤ F.1 ⊔ E.1 from le_sup_left) (le_galoisClosure S)
    have hEM : E ≤ M := le_trans (show E.1 ≤ F.1 ⊔ E.1 from le_sup_right) (le_galoisClosure S)
    rw [← of_ideleClassMap hEM c] at hz ⊢
    let := algebraOfLE hFM
    have : IsScalarTower ℚ F.1 M.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : IsGalois F.1 M.1 := IsGalois.tower_top_of_isGalois ℚ F.1 M.1
    have hfix : ∀ σ : M.1 ≃ₐ[F.1] M.1, σ • FiniteSubfield.ideleClassMap hEM c =
        FiniteSubfield.ideleClassMap hEM c := by
      intro σ
      let σ' : ℚ̄ ≃ₐ[ℚ] ℚ̄ := (σ.restrictScalars ℚ).liftNormal ℚ̄
      have hσ' : ∀ x : M.1, σ' x = σ x := fun x ↦ (σ.restrictScalars ℚ).liftNormal_commutes ℚ̄ x
      have hmem : σ' ∈ F.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have h1 := hσ' (algebraMap F.1 M.1 ⟨x, hx⟩)
        rw [σ.commutes] at h1
        exact h1
      have h1 := hz σ' hmem
      rw [smul_of_eq_of_ideleClassEquiv σ' (σ : M.1 ≃+* M.1) hσ'] at h1
      exact of_injective M h1
    obtain ⟨d, hd⟩ :=
      (forall_smul_eq_iff_mem_range_ideleClassMap (K := F.1) (FiniteSubfield.ideleClassMap hEM c)).1
        hfix
    exact ⟨d, by rw [← hd]; exact (of_ideleClassMap hFM d).symm⟩
  · rintro _ ⟨c, rfl⟩ σ hσ
    exact smul_of_eq_of_mem_fixingSubgroup hσ c

/- English proof (translation)
Establish `h` using `fixedModule_fixingSubgroup (ofOpenSubgroup U)`. Rewrite `h` using `[fixingSubgroup_ofOpenSubgroup]`. Then use the resulting hypothesis.
-/
theorem fixedModule_openSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = (of (ofOpenSubgroup U)).range := by
  have h := fixedModule_fixingSubgroup (ofOpenSubgroup U)
  rwa [fixingSubgroup_ofOpenSubgroup] at h

def fixedEquiv (F : FiniteSubfield) :
    IdeleClassGroup F.1 ≃* fixedModule IdeleClassLimit F.1.fixingSubgroup :=
  (MonoidHom.ofInjective (of_injective F)).trans
    (MulEquiv.subgroupCongr (fixedModule_fixingSubgroup F).symm)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_fixedEquiv (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    (fixedEquiv F c : IdeleClassLimit) = of F c :=
  rfl

/- English proof (translation)
Use `set K := F.1.fixingSubgroup`. Use `set L := E.1.fixingSubgroup`. Set `M` to `galoisClosure E`. Establish `hEM : E ≤ M` using `le_galoisClosure E`. Establish `hFM : F ≤ M` using `le_trans h hEM`.

Set `iFE` to `algebraOfLE h`. Set `iEM` to `algebraOfLE hEM`. Set `iFM` to `algebraOfLE hFM`. Establish `: IsScalarTower F.1 E.1 M.1` using `IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`. Set `ι` to `K ⧸ L.subgroupOf K`.

Set `_ : Fintype ι` to `Fintype.ofFinite ι`. Set `ρ : ι → (M.1 ≃ₐ[F.1] M.1)` to `fun q ↦ AlgEquiv.ofRingEquiv (f := ((((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal M.1 : M.1 ≃ₐ[ℚ] M.1) : M.1 ≃+* M.1)) (fun x ↦ by`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `AlgEquiv.restrictNormal_commutes ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) M.1 (algebraMap F.1 M.1 x)`. Use `h1.trans ?_` and prove the remaining obligations.

Conclude with `(IntermediateField.mem_fixingSubgroup_iff F.1 _).1 (q.out : K).2 x x.2)`. Establish `hρ : ∀ (q : ι) (x : M.1), ((ρ q x : M.1) : ℚ̄) = ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x` using `fun q x ↦ AlgEquiv.restrictNormal_commutes ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) M.1 x`. Establish `hinj : Function.Injective fun q ↦ (ρ q : M.1 →ₐ[F.1] M.1).comp (IsScalarTower.toAlgHom F.1 E.1 M.1)`. Introduce `q q' hqq'`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Establish `h1` using `congrArg (fun f : E.1 →ₐ[F.1] M.1 ↦ ((f ⟨x, hx⟩ : M.1) : ℚ̄)) hqq'`. Simplify using `only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom'] at h1`. Rewrite `h1` using `[hρ, hρ]`. Express the relevant statement in the definitionally equal form `((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x = ((q'.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x at h1`.

Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Establish `hcard : Fintype.card ι = Module.finrank F.1 E.1`. Rewrite using `[← relIndex_fixingSubgroup h, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Establish `hq : ∀ q : ι, cosetSMul IdeleClassLimit K L (fixedEquiv E c) q = of M (ρ q • FiniteSubfield.ideleClassMap hEM c)`.

Introduce `q`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[cosetSMul_mk, coe_fixedEquiv, ← of_ideleClassMap hEM c, smul_of_eq_of_ideleClassEquiv _ (ρ q : M.1 ≃+* M.1) (fun x ↦ (hρ q x).symm)]`. Both sides reduce to the same expression. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[coe_norm, finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun q _ ↦ hq q, ← map_prod, coe_fixedEquiv]`. Establish `h2` using `ideleClassMap_ideleClassNorm_eq_prod ρ hinj hcard c`. Express the relevant statement in the definitionally equal form `_ = of F (GroundTheory.Global.ideleClassNorm F.1 E.1 c)`. Rewrite using `[← of_ideleClassMap hFM]`. Conclude with `congrArg (of M) h2.symm`.
-/
theorem norm_fixedEquiv {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup E.1) :
    norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup (fixedEquiv E c) =
      fixedEquiv F (FiniteSubfield.ideleClassNorm h c) := by
  classical
  set K := F.1.fixingSubgroup
  set L := E.1.fixingSubgroup
  let M := galoisClosure E
  have hEM : E ≤ M := le_galoisClosure E
  have hFM : F ≤ M := le_trans h hEM
  let iFE := algebraOfLE h
  let iEM := algebraOfLE hEM
  let iFM := algebraOfLE hFM
  have : IsScalarTower F.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ι := K ⧸ L.subgroupOf K
  let _ : Fintype ι := Fintype.ofFinite ι
  let ρ : ι → (M.1 ≃ₐ[F.1] M.1) := fun q ↦
    AlgEquiv.ofRingEquiv (f := ((((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal M.1 : M.1 ≃ₐ[ℚ] M.1) :
      M.1 ≃+* M.1)) (fun x ↦ by
        apply Subtype.ext
        have h1 := AlgEquiv.restrictNormal_commutes ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) M.1
          (algebraMap F.1 M.1 x)
        refine h1.trans ?_
        exact (IntermediateField.mem_fixingSubgroup_iff F.1 _).1 (q.out : K).2 x x.2)
  have hρ : ∀ (q : ι) (x : M.1), ((ρ q x : M.1) : ℚ̄) = ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x :=
    fun q x ↦ AlgEquiv.restrictNormal_commutes ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) M.1 x
  have hinj : Function.Injective fun q ↦
      (ρ q : M.1 →ₐ[F.1] M.1).comp (IsScalarTower.toAlgHom F.1 E.1 M.1) := by
    intro q q' hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 := congrArg (fun f : E.1 →ₐ[F.1] M.1 ↦ ((f ⟨x, hx⟩ : M.1) : ℚ̄)) hqq'
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom'] at h1
    rw [hρ, hρ] at h1
    change ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x = ((q'.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x at h1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h1, ← AlgEquiv.mul_apply,
      inv_mul_cancel, AlgEquiv.one_apply]
  have hcard : Fintype.card ι = Module.finrank F.1 E.1 := by
    rw [← relIndex_fixingSubgroup h, ← Nat.card_eq_fintype_card]
    rfl
  have hq : ∀ q : ι, cosetSMul IdeleClassLimit K L (fixedEquiv E c) q =
      of M (ρ q • FiniteSubfield.ideleClassMap hEM c) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [cosetSMul_mk, coe_fixedEquiv, ← of_ideleClassMap hEM c,
      smul_of_eq_of_ideleClassEquiv _ (ρ q : M.1 ≃+* M.1) (fun x ↦ (hρ q x).symm)]
    rfl
  apply Subtype.ext
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun q _ ↦ hq q, ← map_prod,
    coe_fixedEquiv]
  have h2 := ideleClassMap_ideleClassNorm_eq_prod ρ hinj hcard c
  change _ = of F (GroundTheory.Global.ideleClassNorm F.1 E.1 c)
  rw [← of_ideleClassMap hFM]
  exact congrArg (of M) h2.symm

instance normal_range_ideleClassNorm {F E : FiniteSubfield} (h : F ≤ E) :
    (FiniteSubfield.ideleClassNorm h).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def tateZeroEquiv {F E : FiniteSubfield} (h : F ≤ E) :
    tateZero IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup ≃*
      IdeleClassGroup F.1 ⧸ (FiniteSubfield.ideleClassNorm h).range :=
  QuotientGroup.congr (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).range
    (FiniteSubfield.ideleClassNorm h).range (fixedEquiv F).symm (by
    ext c
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      obtain ⟨d, rfl⟩ := (fixedEquiv E).surjective a
      refine ⟨d, ?_⟩
      rw [norm_fixedEquiv h]
      exact ((fixedEquiv F).symm_apply_apply _).symm
    · rintro ⟨d, rfl⟩
      refine ⟨_, ⟨fixedEquiv E d, rfl⟩, ?_⟩
      rw [norm_fixedEquiv h]
      exact (fixedEquiv F).symm_apply_apply _)

/- English proof (translation)
Rewrite using `[tateZeroEquiv, QuotientGroup.congr_mk]`. Conclude with `congrArg _ ((fixedEquiv F).symm_apply_apply c)`.
-/
theorem tateZeroEquiv_mk {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup F.1) :
    tateZeroEquiv h (fixedEquiv F c : tateZero IdeleClassLimit F.1.fixingSubgroup
      E.1.fixingSubgroup) = (c : IdeleClassGroup F.1 ⧸ (FiniteSubfield.ideleClassNorm h).range) := by
  rw [tateZeroEquiv, QuotientGroup.congr_mk]
  exact congrArg _ ((fixedEquiv F).symm_apply_apply c)

end IdeleClassLimit

end

end GroundTheory.Global
