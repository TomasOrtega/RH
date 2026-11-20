import Mathlib

namespace GlobalTheory.CoprimeAbsNorm

open NumberField IsDedekindDomain

/- English proof (translation)
Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `p hp hpm hpN`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : P.asIdeal.IsPrime := P.isPrime`. Use `haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot`.

Establish `hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal)`. Rewrite `hpN` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Then use the resulting hypothesis. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' p hcard`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx` using `[addOrderOf_zero]`. Conclude with `hp.one_lt.ne hx`. Establish `hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx]`. Conclude with `addOrderOf_nsmul_eq_zero x`.

Establish `hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0` using `(mul_eq_zero.mp hpx).resolve_right hx0`. Establish `hpP : (p : RingOfIntegers E) ∈ P.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `hp0`. Take `⟨k, rfl⟩` from `hpm`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hpP`.
-/
theorem coprime_absNorm_of_natCast_notMem {E : Type} [Field E] [NumberField E]
    {P : HeightOneSpectrum (RingOfIntegers E)} {m : ℕ}
    (hm : (m : RingOfIntegers E) ∉ P.asIdeal) :
    Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpN
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0 :=
    (mul_eq_zero.mp hpx).resolve_right hx0
  have hpP : (p : RingOfIntegers E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  obtain ⟨k, rfl⟩ := hpm
  apply hm
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.CoprimeAbsNorm
