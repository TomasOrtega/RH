import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalFixedFieldMapOfFiniteIndex
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFiniteDimensionalFixedFieldMapOfFiniteIndex.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_fixedField_map_of_finiteIndex' : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G), N.FiniteIndex → (∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E)) → FiniteDimensional F (IntermediateField.fixedField (N.map act)) := by
  first | exact @GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex | exact GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex | (intros; apply GlobalTheory.finiteDimensional_fixedField_map_of_finiteIndex <;> assumption)
