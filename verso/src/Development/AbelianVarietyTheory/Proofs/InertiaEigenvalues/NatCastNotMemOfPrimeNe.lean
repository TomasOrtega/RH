import Mathlib

namespace GlobalTheory.NatCastNotMemPrimeIdeal

/- English proof (translation)
Introduce `hpw`. Establish `hc : IsCoprime (q : ℤ) (p : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hne)`. Take `⟨a, b, hab⟩` from `hc`. Establish `h1 : (a : NumberField.RingOfIntegers L) * (q : NumberField.RingOfIntegers L) + (b : NumberField.RingOfIntegers L) * (p : NumberField.RingOfIntegers L) = 1`. Use `congrArg (Int.cast : ℤ → NumberField.RingOfIntegers L) hab` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Apply `w.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← h1]`. Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hqw) (w.asIdeal.mul_mem_left _ hpw)`.
-/
theorem natCast_notMem_of_prime_ne {L : Type} [Field L] [NumberField L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p)
    (hqw : (q : NumberField.RingOfIntegers L) ∈ w.asIdeal) :
    (p : NumberField.RingOfIntegers L) ∉ w.asIdeal := by
  intro hpw
  have hc : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : NumberField.RingOfIntegers L) * (q : NumberField.RingOfIntegers L)
      + (b : NumberField.RingOfIntegers L) * (p : NumberField.RingOfIntegers L) = 1 := by
    have := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers L) hab
    push_cast at this
    exact this
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hqw) (w.asIdeal.mul_mem_left _ hpw)

end GlobalTheory.NatCastNotMemPrimeIdeal
