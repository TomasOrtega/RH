import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

open NumberField Formalism.HC IsDedekindDomain

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem natCast_mem_iff (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ((n : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∣ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem ringChar_prime (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (ringChar (𝓞 K ⧸ la.asIdeal)).Prime := by
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  exact CharP.char_prime_of_ne_zero (𝓞 K ⧸ la.asIdeal) (CharP.ringChar_ne_zero_of_finite _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff :
    ∀ {φ : Frame} (H : HostRaw φ) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)),
      (((H.QS : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∈ H.small) ∧
      (((H.condN : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∣ H.condN) := by
  intro φ H K _ _ la
  refine ⟨?_, natCast_mem_iff K la _⟩
  rw [natCast_mem_iff]
  exact ⟨fun h => Nat.mem_primeFactors.2 ⟨ringChar_prime K la, h, H.QS_pos.ne'⟩,
    fun h => Nat.dvd_of_mem_primeFactors h⟩
