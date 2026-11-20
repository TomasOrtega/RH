import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterEqInducedOfImprimitivitySystem
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BI.character_eq_ind_of_imprimitive` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FCharacterEqInducedOfImprimitivitySystem.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.character_eq_induced_of_imprimitivity_system : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  first | exact @GlobalTheory.BI.character_eq_ind_of_imprimitive | exact GlobalTheory.BI.character_eq_ind_of_imprimitive | (intros; apply GlobalTheory.BI.character_eq_ind_of_imprimitive <;> assumption)
