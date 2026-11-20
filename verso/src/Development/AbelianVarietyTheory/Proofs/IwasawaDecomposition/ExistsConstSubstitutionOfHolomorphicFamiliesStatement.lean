import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstSubstitutionOfHolomorphicFamilies
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_const_substitution_of_holomorphic_families` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsConstSubstitutionOfHolomorphicFamilies.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_const_substitution_of_holomorphic_families' : ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  first | exact @GlobalTheory.exists_const_substitution_of_holomorphic_families | exact GlobalTheory.exists_const_substitution_of_holomorphic_families | (intros; apply GlobalTheory.exists_const_substitution_of_holomorphic_families <;> assumption)
