import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CompactRepField

/- English proof (translation)
Introduce `l _ Γ _ _ _ _ a r hr`. Set `H : Subgroup (GL (Fin a) (PadicAlgCl l))` to `r.range`. Use `haveI : CompactSpace H := by`. Establish `hc : IsCompact (H : Set (GL (Fin a) (PadicAlgCl l)))`. Establish `: (H : Set (GL (Fin a) (PadicAlgCl l))) = Set.range r`.

Use extensionality with `x`. Simplify using `[H]`. Rewrite using `[this]`. Conclude with `isCompact_range hr`. Conclude with `isCompact_iff_compactSpace.1 hc`.

Take `⟨K, hK, hmem⟩` from `exists_finiteDimensional_entries_mem l H a H.subtype fun i j => ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)`. Use `⟨K, hK, fun g i j => ?_⟩` and prove the remaining obligations. Conclude with `hmem ⟨r g, ⟨g, rfl⟩⟩ i j`.
-/
theorem exists_finiteDimensional_entries_mem_of_continuous :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  intro l _ Γ _ _ _ _ a r hr
  let H : Subgroup (GL (Fin a) (PadicAlgCl l)) := r.range
  haveI : CompactSpace H := by
    have hc : IsCompact (H : Set (GL (Fin a) (PadicAlgCl l))) := by
      have : (H : Set (GL (Fin a) (PadicAlgCl l))) = Set.range r := by
        ext x; simp [H]
      rw [this]; exact isCompact_range hr
    exact isCompact_iff_compactSpace.1 hc
  obtain ⟨K, hK, hmem⟩ := exists_finiteDimensional_entries_mem l H a H.subtype
    fun i j => ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)
  refine ⟨K, hK, fun g i j => ?_⟩
  exact hmem ⟨r g, ⟨g, rfl⟩⟩ i j

end GlobalTheory.CompactRepField
