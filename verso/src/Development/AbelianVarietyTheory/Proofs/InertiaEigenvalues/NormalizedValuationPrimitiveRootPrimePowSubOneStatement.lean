import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormalizedValuationPrimitiveRootPrimePowSubOne.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.normalizedValuation_primitiveRoot_prime_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  first | exact @GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | exact GlobalTheory.nval_primitiveRoot_prime_pow_sub_one | (intros; apply GlobalTheory.nval_primitiveRoot_prime_pow_sub_one <;> assumption)
