import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAwayMapSubalgebraBijective
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFinsetAwayMapSubalgebraBijective.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B), (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) → ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C → ∀ b ∈ g, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  first | exact @GlobalTheory.exists_finset_awayMap_subalgebra_bijective | exact GlobalTheory.exists_finset_awayMap_subalgebra_bijective | (intros; apply GlobalTheory.exists_finset_awayMap_subalgebra_bijective <;> assumption)
