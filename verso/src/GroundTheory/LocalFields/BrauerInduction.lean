import Mathlib
import GroundTheory.LocalFields.BrauerInductionAssembly
import GroundTheory.LocalFields.BrauerInductionMonomial

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G] [Fintype G]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsElementary.exists_eq_indLin {K : Subgroup G} (hK : IsElementary K) {χ : K → ℂ}
    (hχ : IsIrrCharacter χ) : ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ := by
  obtain ⟨p, hp, hKp⟩ := hK
  have := hKp.isNilpotent hp
  obtain ⟨L, μ, h⟩ := hχ.exists_eq_indFun_of_isNilpotent
  exact ⟨L, μ, by rw [h, indLin]⟩

end GroundTheory.LocalField
