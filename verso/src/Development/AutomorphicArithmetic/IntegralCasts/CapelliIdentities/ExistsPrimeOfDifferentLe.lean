import Mathlib
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff

attribute [local instance] Subfield.toField._proof_1 SubfieldClass.toField._proof_12 SubringClass.toRing._proof_8

/- English proof (translation)
Introduce `R H v h`. Establish `h1` using `h (Ideal.absNorm_mem _)`. Rewrite `h1` using `[NumberField.absNorm_differentIdeal H.F]`. Establish `h0 : (NumberField.discr H.F).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.F)`. Rewrite `h1` using `[← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Multiset.prod_coe]`.

Take `⟨x, hx, hxv⟩` from `(v.isPrime.multiset_prod_mem_iff_exists_mem _).1 h1`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 (Multiset.mem_coe.1 hx)`. Establish `hpp` using `Nat.prime_of_mem_primeFactorsList hp`. Use `⟨p, hpp, H.der.discr_primes.1 p hpp ?_, hxv⟩` and prove the remaining obligations. Rewrite using `[H.der.discr_sq]`.

Conclude with `(Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactorsList hp)).trans (dvd_pow_self _ two_ne_zero)`.
-/
theorem UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥H.F)),
    differentIdeal ℤ (NumberField.RingOfIntegers ↥H.F) ≤ v.asIdeal →
      ∃ (p : ℕ),
        Nat.Prime p ∧
          p ∣ H.QS * H.q * H.d ∧
            (↑p : NumberField.RingOfIntegers ↥H.F) ∈
              v.asIdeal := by
  intro R H v h
  have h1 := h (Ideal.absNorm_mem _)
  rw [NumberField.absNorm_differentIdeal H.F] at h1
  have h0 : (NumberField.discr H.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.F)
  rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Multiset.prod_coe] at h1
  obtain ⟨x, hx, hxv⟩ := (v.isPrime.multiset_prod_mem_iff_exists_mem _).1 h1
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  refine ⟨p, hpp, H.der.discr_primes.1 p hpp ?_, hxv⟩
  rw [H.der.discr_sq]
  exact (Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactorsList hp)).trans (dvd_pow_self _ two_ne_zero)
