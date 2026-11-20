import Mathlib
import GroundTheory.GlobalFields.FirstInequality.HerbrandClass
import GroundTheory.GlobalFields.FirstInequalityStatement

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in

def ideleClassToCycTateZero (σ : Gal(L/K)) :
    Additive (IdeleClassGroup K) →+
      CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ :=
  (QuotientAddGroup.mk' _).comp ((ideleClassMap K L).toAdditive.codRestrict _ fun c ↦ by
    rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
      sub_eq_zero]
    exact congrArg Additive.ofMul (smul_ideleClassMap σ _))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ideleClassToCycTateZero_apply (σ : Gal(L/K)) (c : Additive (IdeleClassGroup K)) :
    ideleClassToCycTateZero K L σ c = QuotientAddGroup.mk ⟨Additive.ofMul (ideleClassMap K L c.toMul),
      by
        rw [AddMonoidHom.mem_ker, cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply,
          sub_eq_zero]
        exact congrArg Additive.ofMul (smul_ideleClassMap σ _)⟩ :=
  rfl

section Galois

variable [IsGalois K L]

/- English proof (translation)
Rewrite using `[cycNorm_apply, ideleClassMap_ideleClassNorm]`. Simplify using `only [Representation.ofMulDistribMulAction_apply_apply]`. Both sides reduce to the same expression.
-/
theorem cycNorm_ideleClassGroup (c : Additive (IdeleClassGroup L)) :
    cycNorm (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) c =
      Additive.ofMul (ideleClassMap K L (ideleClassNorm K L c.toMul)) := by
  rw [cycNorm_apply, ideleClassMap_ideleClassNorm]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  rfl

/- English proof (translation)
Introduce `x`. Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H y`. Take `⟨y, hy⟩` from `y`. Establish `hfix` using `(mem_ker_cycSubOne_iff _ hσ y).1 hy`.

Take `⟨c, hc⟩` from `(forall_smul_eq_iff_mem_range_ideleClassMap (K := K) y.toMul).1 fun g ↦ congrArg Additive.toMul (hfix g)`. Use `⟨Additive.ofMul c, ?_⟩` and prove the remaining obligations. Rewrite using `[ideleClassToCycTateZero_apply]`. Use `congr 1`. Conclude with `Subtype.ext (by simp [hc])`.
-/
theorem ideleClassToCycTateZero_surjective (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : Function.Surjective (ideleClassToCycTateZero K L σ) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨y, hy⟩ := y
  have hfix := (mem_ker_cycSubOne_iff _ hσ y).1 hy
  obtain ⟨c, hc⟩ := (forall_smul_eq_iff_mem_range_ideleClassMap (K := K) y.toMul).1 fun g ↦
    congrArg Additive.toMul (hfix g)
  refine ⟨Additive.ofMul c, ?_⟩
  rw [ideleClassToCycTateZero_apply]
  congr 1
  exact Subtype.ext (by simp [hc])

/- English proof (translation)
Use extensionality with `c`. Rewrite using `[AddMonoidHom.mem_ker, ideleClassToCycTateZero_apply, KerModRange.mk_eq_zero_iff]`. Express the relevant statement in the definitionally equal form `_ ↔ c.toMul ∈ (ideleClassNorm K L).range`. Rewrite using `[AddMonoidHom.mem_range, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨d, hd⟩`. Rewrite `hd` using `[cycNorm_ideleClassGroup]`. Conclude with `⟨d.toMul, ideleClassMap_injective (congrArg Additive.toMul hd)⟩`. Introduce and unpack `⟨d, hd⟩`. Use `⟨Additive.ofMul d, ?_⟩` and prove the remaining obligations.

Rewrite using `[cycNorm_ideleClassGroup]`. Simplify using `[hd]`.
-/
theorem ker_ideleClassToCycTateZero (σ : Gal(L/K)) :
    (ideleClassToCycTateZero K L σ).ker = Subgroup.toAddSubgroup (ideleClassNorm K L).range := by
  ext c
  rw [AddMonoidHom.mem_ker, ideleClassToCycTateZero_apply, KerModRange.mk_eq_zero_iff]
  change _ ↔ c.toMul ∈ (ideleClassNorm K L).range
  rw [AddMonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨d, hd⟩
    rw [cycNorm_ideleClassGroup] at hd
    exact ⟨d.toMul, ideleClassMap_injective (congrArg Additive.toMul hd)⟩
  · rintro ⟨d, hd⟩
    refine ⟨Additive.ofMul d, ?_⟩
    rw [cycNorm_ideleClassGroup]
    simp [hd]

/- English proof (translation)
Rewrite using `[← Subgroup.index_toAddSubgroup, ← ker_ideleClassToCycTateZero σ, AddSubgroup.index]`. Conclude with `(Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (ideleClassToCycTateZero_surjective σ hσ)).toEquiv).symm`.
-/
theorem natCard_cycTateZero_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) =
      (ideleClassNorm K L).range.index := by
  rw [← Subgroup.index_toAddSubgroup, ← ker_ideleClassToCycTateZero σ, AddSubgroup.index]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (ideleClassToCycTateZero_surjective σ hσ)).toEquiv).symm

/- English proof (translation)
Take `⟨hH, hval⟩` from `IdeleGroup.cycHerbrand_ideleClassGroup (K := K) (L := L) σ hσ`. Use `hH.2` as an intermediate fact. Establish `hpos : Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) ≠ 0` using `Nat.card_pos.ne'`. Use `⟨?_, hpos⟩` and prove the remaining obligations. Rewrite `hval` using `[cycHerbrand_eq, natCard_cycTateZero_ideleClassGroup σ hσ, div_eq_iff (Nat.cast_ne_zero.2 hpos)]`.

Conclude with `hval` after adjusting the coercions.
-/
theorem index_range_ideleClassNorm (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (ideleClassNorm K L).range.index = finrank K L *
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ) ∧
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      ≠ 0 := by
  obtain ⟨hH, hval⟩ := IdeleGroup.cycHerbrand_ideleClassGroup (K := K) (L := L) σ hσ
  have := hH.2
  have hpos : Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      (IdeleClassGroup L)) σ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨?_, hpos⟩
  rw [cycHerbrand_eq, natCard_cycTateZero_ideleClassGroup σ hσ,
    div_eq_iff (Nat.cast_ne_zero.2 hpos)] at hval
  exact_mod_cast hval

/- English proof (translation)
Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := Gal(L/K))`. Take `⟨h, hpos⟩` from `index_range_ideleClassNorm σ hσ`. Rewrite using `[h]`. Conclude with `⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpos), mul_ne_zero Module.finrank_pos.ne' hpos⟩`.
-/
theorem finrank_le_index_range_ideleClassNorm [IsCyclic Gal(L/K)] :
    finrank K L ≤ (ideleClassNorm K L).range.index ∧ (ideleClassNorm K L).range.index ≠ 0 := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [h]
  exact ⟨Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hpos),
    mul_ne_zero Module.finrank_pos.ne' hpos⟩

end Galois

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _`. Take `⟨hle, hne⟩` from `finrank_le_index_range_ideleClassNorm (K := K) (L := L)`. Establish `: (ideleClassNorm K L).range.FiniteIndex` using `⟨hne⟩`. Establish `: Finite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)` using `Subgroup.finite_quotient_of_finiteIndex`. Set `` to `Fintype.ofFinite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)`.

Rewrite using `[ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card]`. Conclude with `hle` after adjusting the coercions.
-/
theorem firstInequality.{u} : FirstInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨hle, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have : (ideleClassNorm K L).range.FiniteIndex := ⟨hne⟩
  have : Finite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) :=
    Subgroup.finite_quotient_of_finiteIndex
  let := Fintype.ofFinite (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card]
  exact_mod_cast hle

end

end GroundTheory.Global
