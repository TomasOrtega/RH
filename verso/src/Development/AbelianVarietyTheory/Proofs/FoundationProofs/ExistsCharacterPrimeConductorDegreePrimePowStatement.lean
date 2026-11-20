import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ord2.PrimeChar.exists_prime_char` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCharacterPrimeConductorDegreePrimePow.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_character_primeConductor_degree_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl), 1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧ Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧ ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) → ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  first | exact @GlobalTheory.Ord2.PrimeChar.exists_prime_char | exact GlobalTheory.Ord2.PrimeChar.exists_prime_char | (intros; apply GlobalTheory.Ord2.PrimeChar.exists_prime_char <;> assumption)
