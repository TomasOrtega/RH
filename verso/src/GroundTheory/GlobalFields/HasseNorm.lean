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
Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := Gal(L/K))`. Take `⟨j, hj⟩` from `hx`. Use `set ρ := Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)`. Use `set c : Additive (IdeleClassGroup L) := Additive.ofMul (IdeleClassGroup.mk L j)`. Establish `hc : c ∈ (cycNorm ρ).ker`.

Rewrite using `[AddMonoidHom.mem_ker, cycNorm_apply]`. Establish `h1 : ∏ g : Gal(L/K), g • IdeleClassGroup.mk L j = 1`. Rewrite using `[← ideleClassMap_ideleClassNorm, ideleClassNorm_mk, hj, IdeleClassGroup.mk_diagonal, map_one]`. Simplify using `only [ρ, c, Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]`. Conclude with `(ofMul_prod Finset.univ _).symm.trans (congrArg Additive.ofMul h1)`.

Establish `hsub : Subsingleton (CycTateNegOne ρ σ)` using `(Nat.card_eq_one_iff_unique.1 (natCard_cycTateNegOne_ideleClassGroup σ hσ)).1`. Establish `h0 : (QuotientAddGroup.mk ⟨c, hc⟩ : CycTateNegOne ρ σ) = 0` using `Subsingleton.elim _ _`. Take `⟨d, hd⟩` from `AddMonoidHom.mem_range.1 ((KerModRange.mk_eq_zero_iff _).1 h0)`. Take `⟨e, he⟩` from `IdeleClassGroup.mk_surjective L (Additive.toMul d)`. Rewrite `hd` using `[cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply]`.

Establish `hjc : IdeleClassGroup.mk L j = IdeleClassGroup.mk L ((σ • e) / e)`. Use `congrArg Additive.toMul hd` as an intermediate fact. Simplify using `only [c, toMul_sub, toMul_ofMul] at this`. Rewrite using `[← this, ← he, map_div, smul_mk]`. Take `⟨a, ha⟩` from `QuotientGroup.eq.1 hjc.symm`.

Use `⟨a, IdeleGroup.diagonal_injective K ?_⟩` and prove the remaining obligations. Rewrite using `[← ideleNorm_diagonal, ha, map_mul, map_inv, map_div, ideleNorm_smul, div_self', inv_one, one_mul, hj]`.
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
Use `⟨?_, mem_range_norm_of_diagonal_mem_range_ideleNorm⟩` and prove the remaining obligations. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨IdeleGroup.diagonal L a, ideleNorm_diagonal a⟩`.
-/
theorem mem_range_norm_iff_diagonal_mem_range_ideleNorm [IsCyclic Gal(L/K)] (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      IdeleGroup.diagonal K x ∈ (ideleNorm K L).range := by
  refine ⟨?_, mem_range_norm_of_diagonal_mem_range_ideleNorm⟩
  rintro ⟨a, rfl⟩
  exact ⟨IdeleGroup.diagonal L a, ideleNorm_diagonal a⟩

/- English proof (translation)
Rewrite using `[mem_range_norm_iff_diagonal_mem_range_ideleNorm, IdeleNorm.mem_range_ideleNorm_iff_forall]`.
-/
theorem mem_range_norm_iff_forall_local [IsCyclic Gal(L/K)] (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  rw [mem_range_norm_iff_diagonal_mem_range_ideleNorm, IdeleNorm.mem_range_ideleNorm_iff_forall]

/- English proof (translation)
Rewrite using `[← mem_range_norm_iff_forall_local]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hx (by simpa using hy.symm)`. Conclude with `⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩`. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, by simpa using congrArg Units.val ha⟩`.
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
Establish `: Algebra.IsQuadraticExtension K L` using `⟨h⟩`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem isGalois_isCyclic_of_finrank_eq_two (h : finrank K L = 2) :
    IsGalois K L ∧ IsCyclic Gal(L/K) := by
  have : Algebra.IsQuadraticExtension K L := ⟨h⟩
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Take `⟨_, _⟩` from `isGalois_isCyclic_of_finrank_eq_two h`. Conclude with `mem_range_norm_iff_diagonal_mem_range_ideleNorm x`.
-/
theorem mem_range_norm_iff_diagonal_mem_range_ideleNorm_of_finrank_eq_two
    (h : finrank K L = 2) (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      IdeleGroup.diagonal K x ∈ (ideleNorm K L).range := by
  obtain ⟨_, _⟩ := isGalois_isCyclic_of_finrank_eq_two h
  exact mem_range_norm_iff_diagonal_mem_range_ideleNorm x

/- English proof (translation)
Take `⟨_, _⟩` from `isGalois_isCyclic_of_finrank_eq_two h`. Conclude with `mem_range_norm_iff_forall_local x`.
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
Take `⟨_, _⟩` from `isGalois_isCyclic_of_finrank_eq_two h`. Conclude with `exists_norm_eq_iff_forall_local hx`.
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
