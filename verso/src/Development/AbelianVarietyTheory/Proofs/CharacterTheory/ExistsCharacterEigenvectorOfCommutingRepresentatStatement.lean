import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FExistsCharacterEigenvectorOfCommutingRepresentat.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_character_eigenvector_of_commuting_representation : ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  first | exact @GlobalTheory.exists_character_eigenvector_of_commute | exact GlobalTheory.exists_character_eigenvector_of_commute | (intros; apply GlobalTheory.exists_character_eigenvector_of_commute <;> assumption)
