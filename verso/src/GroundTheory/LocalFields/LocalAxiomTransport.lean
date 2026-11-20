import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
import GroundTheory.LocalFields.CompleteTrivial

namespace GroundTheory.LocalField.Abstract

open GroundTheory.LocalField (tateNorm invariants mem_invariants TateZero TateNegOne)

section Model

variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
  (K L : Subgroup G) (Γ : Type*) [Group Γ] (M : Type*) [CommGroup M] [MulDistribMulAction Γ M]

structure TateModel where
  le : L ≤ K

  hom : K →* Γ
  surjective_hom : Function.Surjective hom
  ker_hom : hom.ker = L.subgroupOf K

  equiv : fixedModule A L ≃* M

  coe_equiv_symm_smul : ∀ (σ : K) (a : fixedModule A L),
    ((equiv.symm (hom σ • equiv a) : fixedModule A L) : A) = (σ : G) • (a : A)

namespace TateModel

variable {A K L Γ M} (T : TateModel A K L Γ M)

include T in

/- English proof (translation)
The claim follows from `T.ker_hom ▸ T.hom.normal_ker`.
-/
theorem normal : (L.subgroupOf K).Normal :=
  T.ker_hom ▸ T.hom.normal_ker

/- English proof (translation)
Rewrite using `[← T.equiv.apply_symm_apply (T.hom σ • T.equiv a)]`. Use `congr 1`. Conclude with `Subtype.ext (T.coe_equiv_symm_smul σ a).symm`.
-/
theorem equiv_smul (σ : K) (a : fixedModule A L) (h : (σ : G) • (a : A) ∈ fixedModule A L) :
    T.equiv ⟨(σ : G) • (a : A), h⟩ = T.hom σ • T.equiv a := by
  rw [← T.equiv.apply_symm_apply (T.hom σ • T.equiv a)]
  congr 1
  exact Subtype.ext (T.coe_equiv_symm_smul σ a).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha γ`. Take `⟨σ, rfl⟩` from `T.surjective_hom γ`. Establish `h : T.equiv.symm (T.hom σ • T.equiv a) = a` using `Subtype.ext ((T.coe_equiv_symm_smul σ a).trans (ha σ σ.2))`. Rewrite using `[← T.equiv.apply_symm_apply (T.hom σ • T.equiv a), h]`.

Introduce `ha σ hσ`. Rewrite using `[← T.coe_equiv_symm_smul ⟨σ, hσ⟩ a, ha, MulEquiv.symm_apply_apply]`.
-/
theorem mem_fixedModule_iff (a : fixedModule A L) :
    (a : A) ∈ fixedModule A K ↔ T.equiv a ∈ invariants Γ M := by
  constructor
  · intro ha γ
    obtain ⟨σ, rfl⟩ := T.surjective_hom γ
    have h : T.equiv.symm (T.hom σ • T.equiv a) = a :=
      Subtype.ext ((T.coe_equiv_symm_smul σ a).trans (ha σ σ.2))
    rw [← T.equiv.apply_symm_apply (T.hom σ • T.equiv a), h]
  · intro ha σ hσ
    rw [← T.coe_equiv_symm_smul ⟨σ, hσ⟩ a, ha, MulEquiv.symm_apply_apply]

def fixedModuleEquiv : fixedModule A K ≃* invariants Γ M where
  toFun a := ⟨T.equiv ⟨a, fixedModule_anti T.le a.2⟩,
    (T.mem_fixedModule_iff ⟨a, fixedModule_anti T.le a.2⟩).1 a.2⟩
  invFun m := ⟨T.equiv.symm m, (T.mem_fixedModule_iff _).2 (by simp [m.2])⟩
  left_inv a := by simp
  right_inv m := by simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul]
    rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_fixedModuleEquiv (a : fixedModule A K) :
    (T.fixedModuleEquiv a : M) = T.equiv ⟨a, fixedModule_anti T.le a.2⟩ :=
  rfl

variable [(L.subgroupOf K).Normal]

noncomputable def quotientEquiv : K ⧸ L.subgroupOf K ≃* Γ :=
  (QuotientGroup.quotientMulEquivOfEq T.ker_hom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective T.hom T.surjective_hom)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotientEquiv_mk (σ : K) : T.quotientEquiv (σ : K ⧸ L.subgroupOf K) = T.hom σ :=
  rfl

include T in

/- English proof (translation)
The claim follows from `Nat.card_congr T.quotientEquiv.toEquiv`.
-/
theorem relIndex_eq_natCard : L.relIndex K = Nat.card Γ :=
  Nat.card_congr T.quotientEquiv.toEquiv

/- English proof (translation)
Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H σ`. Establish `h` using `smul_mem_fixedModule_of_normal T.le σ.2 a.2`. Conclude with `⟨h, T.equiv_smul σ a h⟩`.
-/
theorem exists_cosetSMul (a : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    ∃ h : cosetSMul A K L a q ∈ fixedModule A L,
      T.equiv ⟨cosetSMul A K L a q, h⟩ = T.quotientEquiv q • T.equiv a := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    have h := smul_mem_fixedModule_of_normal T.le σ.2 a.2
    exact ⟨h, T.equiv_smul σ a h⟩

/- English proof (translation)
Set `_` to `Fintype.ofFinite (K ⧸ L.subgroupOf K)`. Use `choose hmem hval using T.exists_cosetSMul a`. Establish `hprod : (⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ : fixedModule A L) = ∏ q, (⟨cosetSMul A K L a q, hmem q⟩ : fixedModule A L)`. Use `ext`. Rewrite using `[coe_norm, finprod_eq_prod_of_fintype, Subgroup.val_finsetProd]`.

Rewrite using `[hprod, map_prod, GroundTheory.LocalField.tateNorm_apply]`. Repeatedly rewrite using `[hval]`. Conclude with `Fintype.prod_equiv T.quotientEquiv.toEquiv _ _ fun _ => rfl`.
-/
theorem norm_eq [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : fixedModule A L) :
    T.equiv ⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ = tateNorm Γ M (T.equiv a) := by
  classical
  let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
  choose hmem hval using T.exists_cosetSMul a
  have hprod : (⟨norm A K L a, fixedModule_anti T.le (norm A K L a).2⟩ : fixedModule A L) =
      ∏ q, (⟨cosetSMul A K L a q, hmem q⟩ : fixedModule A L) := by
    ext
    rw [coe_norm, finprod_eq_prod_of_fintype, Subgroup.val_finsetProd]
  rw [hprod, map_prod, GroundTheory.LocalField.tateNorm_apply]
  simp_rw [hval]
  exact Fintype.prod_equiv T.quotientEquiv.toEquiv _ _ fun _ => rfl

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, rfl⟩, rfl⟩`. Conclude with `⟨T.equiv a, by rw [coe_fixedModuleEquiv, T.norm_eq]⟩`.

Introduce and unpack `⟨x, hx⟩`. Use `⟨_, ⟨T.equiv.symm x, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_fixedModuleEquiv, T.norm_eq, MulEquiv.apply_symm_apply, hx]`.
-/
theorem map_range_norm [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).range.map T.fixedModuleEquiv.toMonoidHom =
      (tateNorm Γ M).range.subgroupOf (invariants Γ M) := by
  ext m
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨T.equiv a, by rw [coe_fixedModuleEquiv, T.norm_eq]⟩
  · rintro ⟨x, hx⟩
    refine ⟨_, ⟨T.equiv.symm x, rfl⟩, Subtype.ext ?_⟩
    rw [coe_fixedModuleEquiv, T.norm_eq, MulEquiv.apply_symm_apply, hx]

noncomputable def tateZeroEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    tateZero A K L ≃* TateZero Γ M :=
  QuotientGroup.congr _ _ T.fixedModuleEquiv T.map_range_norm

include T in
/- English proof (translation)
The claim follows from `Nat.card_congr T.tateZeroEquiv.toEquiv`.
-/
theorem natCard_tateZero [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateZero A K L) = Nat.card (TateZero Γ M) :=
  Nat.card_congr T.tateZeroEquiv.toEquiv

/- English proof (translation)
Rewrite using `[← T.norm_eq, MulEquiv.map_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `ext`. Simplify using `[h]`.

Introduce `h`. Conclude with `Subtype.ext (by simpa using congrArg Subtype.val h)`.
-/
theorem norm_eq_one_iff [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : fixedModule A L) :
    norm A K L a = 1 ↔ tateNorm Γ M (T.equiv a) = 1 := by
  rw [← T.norm_eq, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    ext
    simp [h]
  · intro h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [Subgroup.mem_map, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `(T.norm_eq_one_iff a).1 ha`.

Introduce `hm`. Conclude with `⟨T.equiv.symm m, (T.norm_eq_one_iff _).2 (by simpa using hm), by simp⟩`.
-/
theorem map_ker_norm [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).ker.map T.equiv.toMonoidHom = (tateNorm Γ M).ker := by
  ext m
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (T.norm_eq_one_iff a).1 ha
  · intro hm
    exact ⟨T.equiv.symm m, (T.norm_eq_one_iff _).2 (by simpa using hm), by simp⟩

omit [(L.subgroupOf K).Normal] in

/- English proof (translation)
Rewrite using `[augmentation, GroundTheory.LocalField.augmentation, MonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_image, MonoidHom.coe_comp, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, Function.comp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, a, ha, rfl⟩`. Use `⟨T.hom ⟨g, hg⟩ • T.equiv ⟨a, ha⟩ / T.equiv ⟨a, ha⟩, ⟨_, _, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div, Subgroup.coe_div, T.coe_equiv_symm_smul, MulEquiv.symm_apply_apply]`. Introduce and unpack `⟨_, ⟨γ, m, rfl⟩, rfl⟩`. Take `⟨σ, rfl⟩` from `T.surjective_hom γ`.

Use `⟨σ, σ.2, T.equiv.symm m, (T.equiv.symm m).2, ?_⟩` and prove the remaining obligations. Establish `h` using `T.coe_equiv_symm_smul σ (T.equiv.symm m)`. Rewrite `h` using `[MulEquiv.apply_symm_apply]`. Rewrite using `[map_div, Subgroup.coe_div, h]`.
-/
theorem augmentation_eq_map :
    augmentation A K L =
      (GroundTheory.LocalField.augmentation Γ M).map
        ((fixedModule A L).subtype.comp T.equiv.symm.toMonoidHom) := by
  rw [augmentation, GroundTheory.LocalField.augmentation, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, MonoidHom.coe_comp, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, Function.comp_apply]
  constructor
  · rintro ⟨g, hg, a, ha, rfl⟩
    refine ⟨T.hom ⟨g, hg⟩ • T.equiv ⟨a, ha⟩ / T.equiv ⟨a, ha⟩, ⟨_, _, rfl⟩, ?_⟩
    rw [map_div, Subgroup.coe_div, T.coe_equiv_symm_smul, MulEquiv.symm_apply_apply]
  · rintro ⟨_, ⟨γ, m, rfl⟩, rfl⟩
    obtain ⟨σ, rfl⟩ := T.surjective_hom γ
    refine ⟨σ, σ.2, T.equiv.symm m, (T.equiv.symm m).2, ?_⟩
    have h := T.coe_equiv_symm_smul σ (T.equiv.symm m)
    rw [MulEquiv.apply_symm_apply] at h
    rw [map_div, Subgroup.coe_div, h]

omit [(L.subgroupOf K).Normal] in

/- English proof (translation)
Rewrite using `[T.augmentation_eq_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, h⟩`. Establish `: T.equiv.symm m = a` using `Subtype.ext h`. Rewrite using `[← this, MulEquiv.apply_symm_apply]`.

Conclude with `hm`. Introduce `h`. Conclude with `⟨T.equiv a, h, by simp⟩`.
-/
theorem mem_augmentation_iff (a : fixedModule A L) :
    (a : A) ∈ augmentation A K L ↔ T.equiv a ∈ GroundTheory.LocalField.augmentation Γ M := by
  rw [T.augmentation_eq_map]
  constructor
  · rintro ⟨m, hm, h⟩
    have : T.equiv.symm m = a := Subtype.ext h
    rw [← this, MulEquiv.apply_symm_apply]
    exact hm
  · intro h
    exact ⟨T.equiv a, h, by simp⟩

noncomputable def kerEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    (norm A K L).ker ≃* (tateNorm Γ M).ker :=
  (T.equiv.subgroupMap (norm A K L).ker).trans (MulEquiv.subgroupCongr T.map_ker_norm)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_kerEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] (a : (norm A K L).ker) :
    (T.kerEquiv a : M) = T.equiv a :=
  rfl

noncomputable def tateNegOneEquiv [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    tateNegOne A K L ≃* TateNegOne Γ M :=
  QuotientGroup.congr _ _ T.kerEquiv <| by
    ext m
    obtain ⟨a, rfl⟩ := T.kerEquiv.surjective m
    simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_subgroupOf, MonoidHom.coe_comp,
      Subgroup.coe_subtype, Function.comp_apply, coe_kerEquiv]
    constructor
    · rintro ⟨x, hx, hxa⟩
      rw [T.kerEquiv.injective hxa] at hx
      exact (T.mem_augmentation_iff _).1 hx
    · intro h
      exact ⟨a, (T.mem_augmentation_iff _).2 h, rfl⟩

include T in
/- English proof (translation)
The claim follows from `Nat.card_congr T.tateNegOneEquiv.toEquiv`.
-/
theorem natCard_tateNegOne [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateNegOne A K L) = Nat.card (TateNegOne Γ M) :=
  Nat.card_congr T.tateNegOneEquiv.toEquiv

end TateModel

end Model

end GroundTheory.LocalField.Abstract
