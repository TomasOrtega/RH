import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntGeneratorsCardEqOfIsLatticePi
import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsIntGeneratorsCardEqOfIsLatticePi.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_int_span_generators_of_isLattice_pi : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E, (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | exact GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | (intros; apply GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi <;> assumption)
