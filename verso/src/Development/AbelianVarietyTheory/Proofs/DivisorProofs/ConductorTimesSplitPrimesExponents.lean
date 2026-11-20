import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.CondExp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨q, hq, hd⟩` from `(v.prime.dvd_finset_prod_iff _).1 h`. Establish `: q.asIdeal = v.asIdeal` using `q.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)`. Rewrite using `[← HeightOneSpectrum.ext this]` and apply the resulting hypothesis.

Introduce `h`. Conclude with `Finset.dvd_prod_of_mem _ h`.
-/
theorem dvd_prod_primes_iff {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ q ∈ Q, q.asIdeal ↔ v ∈ Q := by
  constructor
  · intro h
    obtain ⟨q, hq, hd⟩ := (v.prime.dvd_finset_prod_iff _).1 h
    have : q.asIdeal = v.asIdeal :=
      q.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)
    rwa [← HeightOneSpectrum.ext this]
  · intro h
    exact Finset.dvd_prod_of_mem _ h

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot`.
-/
theorem prod_primes_ne_zero {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) : ∏ q ∈ Q, q.asIdeal ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot

/- English proof (translation)
Establish `h0` using `prod_primes_ne_zero Q`. Rewrite `h0`, the goal using `[← Finset.mul_prod_erase Q _ hv]`. Rewrite using `[multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0), multiplicity_self, multiplicity_eq_zero.2 (by rw [dvd_prod_primes_iff]; simp)]`.
-/
theorem multiplicity_prod_primes_of_mem {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) (hv : v ∈ Q) :
    multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) = 1 := by
  classical
  have h0 := prod_primes_ne_zero Q
  rw [← Finset.mul_prod_erase Q _ hv] at h0 ⊢
  rw [multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0), multiplicity_self,
    multiplicity_eq_zero.2 (by rw [dvd_prod_primes_iff]; simp)]

/- English proof (translation)
Introduce `E _ _ 𝔣 Q hb ha`. Establish `h0 : condQ 𝔣 Q ≠ 0` using `mul_ne_zero hb.1 (prod_primes_ne_zero Q)`. Establish `hm : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v = expIn 𝔣 v + multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal)` using `fun v => multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0)`. Establish `hd : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q`. Introduce `v hv`.

Assume the negation of the conclusion as `h`. Conclude with `hv (multiplicity_eq_zero.2 h)`. Use `⟨h0, ?_, hd, ?_, ?_, (Ideal.finite_factors h0).subset hd⟩` and prove the remaining obligations. Introduce `v hv`. Break down `v.prime.dvd_or_dvd hv with h | h` into its components or cases.

Conclude with `(hb.2.2 v h).1`. Conclude with `(ha v ((dvd_prod_primes_iff Q v).1 h)).1`. Introduce `v hv`. Establish `h1 : expIn 𝔣 v = 0` using `multiplicity_eq_zero.2 (ha v hv).2`. Rewrite using `[hm, h1, multiplicity_prod_primes_of_mem Q v hv]`.

Introduce `v hv`. Rewrite using `[hm, multiplicity_eq_zero.2 (fun h => hv ((dvd_prod_primes_iff Q v).1 h)), add_zero]`.
-/
theorem condQ_exponents : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  intro E _ _ 𝔣 Q hb ha
  have h0 : condQ 𝔣 Q ≠ 0 := mul_ne_zero hb.1 (prod_primes_ne_zero Q)
  have hm : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v =
      expIn 𝔣 v + multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) := fun v =>
    multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0)
  have hd : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q := by
    intro v hv
    by_contra h
    exact hv (multiplicity_eq_zero.2 h)
  refine ⟨h0, ?_, hd, ?_, ?_, (Ideal.finite_factors h0).subset hd⟩
  · intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact (hb.2.2 v h).1
    · exact (ha v ((dvd_prod_primes_iff Q v).1 h)).1
  · intro v hv
    have h1 : expIn 𝔣 v = 0 := multiplicity_eq_zero.2 (ha v hv).2
    rw [hm, h1, multiplicity_prod_primes_of_mem Q v hv]
  · intro v hv
    rw [hm, multiplicity_eq_zero.2 (fun h => hv ((dvd_prod_primes_iff Q v).1 h)), add_zero]

end GlobalTheory.CMVal.CondExp
