import Mathlib
import GroundTheory.GlobalFields.SecondInequality.Cyclic
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module IsDedekindDomain AdeleBaseChange

universe u

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_range_norm_of_diagonal_mem_range_ideleNorm [IsCyclic Gal(L/K)] {x : Kˣ}
    (hx : IdeleGroup.diagonal K x ∈ (ideleNorm K L).range) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨j, hj⟩ := hx
  set ρ := Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)
  set c : Additive (IdeleClassGroup L) := Additive.ofMul (IdeleClassGroup.mk L j)

  have hc : c ∈ (cycNorm ρ).ker := by
    rw [AddMonoidHom.mem_ker, cycNorm_apply]
    have h1 : ∏ g : Gal(L/K), g • IdeleClassGroup.mk L j = 1 := by
      rw [← ideleClassMap_ideleClassNorm, ideleClassNorm_mk, hj, IdeleClassGroup.mk_diagonal,
        map_one]
    simp only [ρ, c, Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
    exact (ofMul_prod Finset.univ _).symm.trans (congrArg Additive.ofMul h1)

  have hsub : Subsingleton (CycTateNegOne ρ σ) :=
    (Nat.card_eq_one_iff_unique.1 (natCard_cycTateNegOne_ideleClassGroup σ hσ)).1
  have h0 : (QuotientAddGroup.mk ⟨c, hc⟩ : CycTateNegOne ρ σ) = 0 := Subsingleton.elim _ _
  obtain ⟨d, hd⟩ := AddMonoidHom.mem_range.1 ((KerModRange.mk_eq_zero_iff _).1 h0)
  obtain ⟨e, he⟩ := IdeleClassGroup.mk_surjective L (Additive.toMul d)
  rw [cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply] at hd
  have hjc : IdeleClassGroup.mk L j = IdeleClassGroup.mk L ((σ • e) / e) := by
    have := congrArg Additive.toMul hd
    simp only [c, toMul_sub, toMul_ofMul] at this
    rw [← this, ← he, map_div, smul_mk]

  obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hjc.symm
  refine ⟨a, IdeleGroup.diagonal_injective K ?_⟩
  rw [← ideleNorm_diagonal, ha, map_mul, map_inv, map_div, ideleNorm_smul, div_self', inv_one,
    one_mul, hj]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem mem_range_norm_iff_diagonal_mem_range_ideleNorm [IsCyclic Gal(L/K)] (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      IdeleGroup.diagonal K x ∈ (ideleNorm K L).range := by
  refine ⟨?_, mem_range_norm_of_diagonal_mem_range_ideleNorm⟩
  rintro ⟨a, rfl⟩
  exact ⟨IdeleGroup.diagonal L a, ideleNorm_diagonal a⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_range_norm_iff_forall_local [IsCyclic Gal(L/K)] (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  rw [mem_range_norm_iff_diagonal_mem_range_ideleNorm, IdeleNorm.mem_range_ideleNorm_iff_forall]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_norm_eq_iff_forall_local [IsCyclic Gal(L/K)] {x : K} (hx : x ≠ 0) :
    (∃ y : L, Algebra.norm K y = x) ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K (Units.mk0 x hx)) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K (Units.mk0 x hx)) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  rw [← mem_range_norm_iff_forall_local]
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hy.symm)
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa using congrArg Units.val ha⟩

end

section Quadratic

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem isGalois_isCyclic_of_finrank_eq_two (h : finrank K L = 2) :
    IsGalois K L ∧ IsCyclic Gal(L/K) := by
  have : Algebra.IsQuadraticExtension K L := ⟨h⟩
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem mem_range_norm_iff_diagonal_mem_range_ideleNorm_of_finrank_eq_two
    (h : finrank K L = 2) (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      IdeleGroup.diagonal K x ∈ (ideleNorm K L).range := by
  obtain ⟨_, _⟩ := isGalois_isCyclic_of_finrank_eq_two h
  exact mem_range_norm_iff_diagonal_mem_range_ideleNorm x

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem mem_range_norm_iff_forall_local_of_finrank_eq_two (h : finrank K L = 2) (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  obtain ⟨_, _⟩ := isGalois_isCyclic_of_finrank_eq_two h
  exact mem_range_norm_iff_forall_local x

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exists_norm_eq_iff_forall_local_of_finrank_eq_two (h : finrank K L = 2) {x : K}
    (hx : x ≠ 0) :
    (∃ y : L, Algebra.norm K y = x) ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K (Units.mk0 x hx)) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K (Units.mk0 x hx)) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  obtain ⟨_, _⟩ := isGalois_isCyclic_of_finrank_eq_two h
  exact exists_norm_eq_iff_forall_local hx

end Quadratic

end GroundTheory.Global
