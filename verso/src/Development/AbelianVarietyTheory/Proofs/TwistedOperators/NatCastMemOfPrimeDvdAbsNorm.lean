import Mathlib

namespace GlobalTheory.NatCastMemOfPrimeDvdNorm

open NumberField IsDedekindDomain

/- English proof (translation)
Use `haveI : Fact q.Prime := ⟨hq⟩`. Use `haveI : w.asIdeal.IsPrime := w.isPrime`. Use `haveI : Finite (RingOfIntegers K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot`. Establish `hc : q ∣ Nat.card (RingOfIntegers K ⧸ w.asIdeal)`. Rewrite `hd` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Then use the resulting hypothesis.

Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' q hc`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx` using `[addOrderOf_zero]`. Conclude with `hq.one_lt.ne hx`.

Establish `h1 : (q : RingOfIntegers K ⧸ w.asIdeal) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx]`. Conclude with `addOrderOf_nsmul_eq_zero x`. Establish `h2 : (q : RingOfIntegers K ⧸ w.asIdeal) = 0` using `(mul_eq_zero.mp h1).resolve_right hx0`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Conclude with `h2`.
-/
theorem natCast_mem_of_prime_dvd_absNorm {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (RingOfIntegers K)) {q : ℕ} (hq : Nat.Prime q)
    (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : RingOfIntegers K) ∈ w.asIdeal := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (RingOfIntegers K ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hc : q ∣ Nat.card (RingOfIntegers K ⧸ w.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : (q : RingOfIntegers K ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have h2 : (q : RingOfIntegers K ⧸ w.asIdeal) = 0 := (mul_eq_zero.mp h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

end GlobalTheory.NatCastMemOfPrimeDvdNorm
