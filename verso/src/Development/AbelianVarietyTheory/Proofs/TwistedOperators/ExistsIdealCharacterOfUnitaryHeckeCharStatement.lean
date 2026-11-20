import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIdealCharacterOfUnitaryHeckeChar.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ ∧ X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ (∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0) ∧ ∀ (β : 𝓞 K) (k : Kˣ), (k : K) = β → β - 1 ∈ m → X (Ideal.span {β}) = (((χ.inf k : ℂˣ) : ℂ))⁻¹ := by
  first | exact @GlobalTheory.exists_ideal_character_of_unitary_hchar | exact GlobalTheory.exists_ideal_character_of_unitary_hchar | (intros; apply GlobalTheory.exists_ideal_character_of_unitary_hchar <;> assumption)
