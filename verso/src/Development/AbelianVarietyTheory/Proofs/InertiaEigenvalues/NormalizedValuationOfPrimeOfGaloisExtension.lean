import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.Eisenstein
import GroundTheory.LocalFields.LowerIndex

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `F L _ _ _ _ _ _ _ _ _ _ _ _ p E h`. Unfold `OrdIs at h ⊢`. Establish `hmap` using `addVal_algebraMap_integer F L (p : 𝒪[F])`. Rewrite `hmap` using `[map_natCast]`. Rewrite `h` using `[hmap]`.

Establish `hne : IsDiscreteValuationRing.addVal 𝒪[F] (p : 𝒪[F]) ≠ ⊤`. Introduce `ht`. Rewrite `h` using `[ht, ENat.mul_top (by exact_mod_cast (ramificationIndex_pos F L).ne')]`. Conclude with `ENat.coe_ne_top E h.symm`. Take `⟨e, he⟩` from `ENat.ne_top_iff_exists.mp hne`.

Use `⟨e, he.symm, ?_, (card_lowerRamificationGroup_zero F L).symm⟩` and prove the remaining obligations. Rewrite `h` using `[← he]`. Conclude with `h.symm` after adjusting the coercions.
-/
theorem ordIs_of_ordIs_ext : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = ramificationIndex F L * e ∧ ramificationIndex F L = Nat.card ↥(lowerRamificationGroup F L 0) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E h
  unfold OrdIs at h ⊢
  have hmap := addVal_algebraMap_integer F L (p : 𝒪[F])
  rw [map_natCast] at hmap
  rw [hmap] at h
  have hne : IsDiscreteValuationRing.addVal 𝒪[F] (p : 𝒪[F]) ≠ ⊤ := by
    intro ht
    rw [ht, ENat.mul_top (by exact_mod_cast (ramificationIndex_pos F L).ne')] at h
    exact ENat.coe_ne_top E h.symm
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨e, he.symm, ?_, (card_lowerRamificationGroup_zero F L).symm⟩
  rw [← he] at h
  exact_mod_cast h.symm

end GlobalTheory.PMon.Ram
