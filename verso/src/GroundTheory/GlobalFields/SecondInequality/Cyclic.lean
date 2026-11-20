import Mathlib
import GroundTheory.GlobalFields.FirstInequality
import GroundTheory.GlobalFields.SecondInequality.PowFinrankMemRangeInfiniteLocalNorm
import GroundTheory.GlobalFields.SecondInequality.Reduction

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

universe u

/- English proof (translation)
The claim follows from `(firstInequality.{u}.secondInequalityRoots).secondInequality`.
-/
theorem secondInequality : SecondInequality.{u} :=
  (firstInequality.{u}.secondInequalityRoots).secondInequality

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/- English proof (translation)
Take `⟨hge, hne⟩` from `finrank_le_index_range_ideleClassNorm (K := K) (L := L)`. Establish `hle` using `((enatCard_quotient_le_iff _ _).1 (secondInequality.{u} K L)).2`. Conclude with `le_antisymm hle hge`.
-/
theorem index_range_ideleClassNorm_eq_finrank [IsCyclic Gal(L/K)] :
    (ideleClassNorm K L).range.index = finrank K L := by
  obtain ⟨hge, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have hle := ((enatCard_quotient_le_iff _ _).1 (secondInequality.{u} K L)).2
  exact le_antisymm hle hge

/- English proof (translation)
Establish `: IsCyclic Gal(L/K)` using `⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩`. Take `⟨h, hpos⟩` from `index_range_ideleClassNorm σ hσ`. Rewrite `h` using `[index_range_ideleClassNorm_eq_finrank]`. Establish `hn : 0 < finrank K L` using `finrank_pos`. Establish `h' : finrank K L * 1 = finrank K L * _` using `(mul_one _).trans h`.

Conclude with `(Nat.eq_of_mul_eq_mul_left hn h').symm`.
-/
theorem natCard_cycTateNegOne_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = 1 := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [index_range_ideleClassNorm_eq_finrank] at h
  have hn : 0 < finrank K L := finrank_pos
  have h' : finrank K L * 1 = finrank K L * _ := (mul_one _).trans h
  exact (Nat.eq_of_mul_eq_mul_left hn h').symm

/- English proof (translation)
Establish `: IsCyclic Gal(L/K)` using `⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩`. Rewrite using `[natCard_cycTateZero_ideleClassGroup σ hσ, index_range_ideleClassNorm_eq_finrank]`.
-/
theorem natCard_cycTateZero_ideleClassGroup_eq_finrank (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = finrank K L := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  rw [natCard_cycTateZero_ideleClassGroup σ hσ, index_range_ideleClassNorm_eq_finrank]

/- English proof (translation)
Assemble the required witnesses or components as `⟨natCard_cycTateZero_ideleClassGroup_eq_finrank σ hσ, natCard_cycTateNegOne_ideleClassGroup σ hσ⟩`.
-/
theorem classFieldAxiom_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = finrank K L ∧
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = 1 :=
  ⟨natCard_cycTateZero_ideleClassGroup_eq_finrank σ hσ, natCard_cycTateNegOne_ideleClassGroup σ hσ⟩

end

end GroundTheory.Global
