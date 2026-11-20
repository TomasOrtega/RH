import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWhittakerJacquetIdempotentsPropertiesPrimeField.lean&line=366#L366)
-/
theorem _root_.GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField : ∀ (g : ℕ) [Fact g.Prime] (N k s : ℕ) (ψ : AddChar (ZMod g) ℂ), eU g N ψ * eU g N ψ = eU g N ψ ∧ (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ ∧ (N = k + 2 * s + 1 → eJ g N k s ψ * eJ g N k s ψ = eJ g N k s ψ ∧ (eJ g N k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) ∧ (k < N → eJ' g N k ψ * eJ' g N k ψ = eJ' g N k ψ ∧ (eJ' g N k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) := by
  first | exact @GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | exact GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField | (intros; apply GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField <;> assumption)
