import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharacterDecompositionAndClassFunctionExpansion.lean&line=254#L254)
-/
theorem _root_.GlobalTheory.T.character_decomposition_and_classFunction_expansion : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsChar χ → ∃ L : List (G → ℂ), (∀ ρ ∈ L, IsIrr ρ) ∧ χ = L.sum) ∧ (IsClass χ → χ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip χ ρ • ρ) ∧ (IsChar χ → IsClass χ) ∧ (IsChar χ → ip χ χ = 1 → IsIrr χ) ∧ (∀ L : List (G → ℂ), (∀ ρ ∈ L, IsChar ρ) → IsChar L.sum) := by
  first | exact @GlobalTheory.charDec | exact GlobalTheory.charDec | (intros; apply GlobalTheory.charDec <;> assumption)
