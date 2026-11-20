import Mathlib
import GroundTheory.GlobalFields.FirstInequality
import GroundTheory.GlobalFields.SecondInequality.PowFinrankMemRangeInfiniteLocalNorm
import GroundTheory.GlobalFields.SecondInequality.Reduction

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module

universe u

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secondInequality : SecondInequality.{u} :=
  (firstInequality.{u}.secondInequalityRoots).secondInequality

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem index_range_ideleClassNorm_eq_finrank [IsCyclic Gal(L/K)] :
    (ideleClassNorm K L).range.index = finrank K L := by
  obtain ⟨hge, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have hle := ((enatCard_quotient_le_iff _ _).1 (secondInequality.{u} K L)).2
  exact le_antisymm hle hge

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem natCard_cycTateZero_ideleClassGroup_eq_finrank (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = finrank K L := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  rw [natCard_cycTateZero_ideleClassGroup σ hσ, index_range_ideleClassNorm_eq_finrank]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem classFieldAxiom_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = finrank K L ∧
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = 1 :=
  ⟨natCard_cycTateZero_ideleClassGroup_eq_finrank σ hσ, natCard_cycTateNegOne_ideleClassGroup σ hσ⟩

end

end GroundTheory.Global
