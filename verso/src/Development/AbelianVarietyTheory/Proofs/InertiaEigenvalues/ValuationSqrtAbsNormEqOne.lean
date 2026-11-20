import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ A p hp hpA P hpP`. Use `set N : ℕ := Ideal.absNorm P.asIdeal with hNdef`. Establish `hNcard : N = Nat.card (𝓞 K ⧸ P.asIdeal)`. Rewrite using `[hNdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hN0 : N ≠ 0`.

Rewrite using `[hNdef, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `P.ne_bot`. Establish `hpN : ¬ p ∣ N`. Introduce `hdvd`. Use `haveI : Finite (𝓞 K ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hNcard ▸ hN0)`.

Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) p (hNcard ▸ hdvd)`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx` using `[addOrderOf_zero]`. Conclude with `hp.one_lt.ne' hx.symm`. Establish `hpx : (p : 𝓞 K ⧸ P.asIdeal) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]`. Establish `hp0 : (p : 𝓞 K ⧸ P.asIdeal) = 0` using `(mul_eq_zero.mp hpx).resolve_right hx0`.

Apply `hpP` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `hp0`. Establish `hcop : Nat.Coprime N p` using `(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN))`. Establish `hbez : (N : ℤ) * Nat.gcdA N p + (p : ℤ) * Nat.gcdB N p = 1`.

Use `Nat.gcd_eq_gcd_ab N p` as an intermediate fact. Rewrite `this` using `[hcop]`. Simplify using `using this.symm`. Establish `hbezA : ((N : A) * ((Nat.gcdA N p : ℤ) : A)) + ((p : A) * ((Nat.gcdB N p : ℤ) : A)) = 1`. Use `congrArg (Int.cast : ℤ → A) hbez` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hpnu : ¬ IsUnit (p : A)`. Rewrite using `[ValuationSubring.valuation_eq_one_iff]`. Use `(ValuationSubring.mem_nonunits_iff A).mp hpA` as an intermediate fact.

Use `push_cast`. Conclude with `this.ne`. Establish `hNu : IsUnit (N : A)`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one hbezA with h | h` into its components or cases. Conclude with `isUnit_of_mul_isUnit_left h`.

Conclude with `absurd (isUnit_of_mul_isUnit_left h) hpnu`. Establish `hvN : A.valuation (N : ℂ) = 1`. Use `(ValuationSubring.valuation_eq_one_iff A _).mp hNu` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `hsq : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`. Establish `h2 : A.valuation ((Real.sqrt N : ℝ) : ℂ) ^ 2 = 1`. Rewrite using `[← map_pow, hsq, hvN]`. Break down `lt_trichotomy (A.valuation ((Real.sqrt N : ℝ) : ℂ)) 1 with h | h | h` into its components or cases.

Conclude with `absurd h2 (pow_lt_one₀ zero_le' h two_ne_zero).ne`. Conclude with `h`. Conclude with `absurd h2 (one_lt_pow₀ h two_ne_zero).ne'`.
-/
theorem valuation_sqrt_absNorm_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
        A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  intro K _ _ A p hp hpA P hpP
  set N : ℕ := Ideal.absNorm P.asIdeal with hNdef

  have hNcard : N = Nat.card (𝓞 K ⧸ P.asIdeal) := by
    rw [hNdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hpN : ¬ p ∣ N := by
    intro hdvd
    haveI : Finite (𝓞 K ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hNcard ▸ hN0)
    haveI : Fact p.Prime := ⟨hp⟩
    letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) p (hNcard ▸ hdvd)
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne' hx.symm
    have hpx : (p : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hp0 : (p : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.mp hpx).resolve_right hx0
    apply hpP
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
  have hcop : Nat.Coprime N p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN))

  have hbez : (N : ℤ) * Nat.gcdA N p + (p : ℤ) * Nat.gcdB N p = 1 := by
    have := Nat.gcd_eq_gcd_ab N p
    rw [hcop] at this; simpa using this.symm
  have hbezA : ((N : A) * ((Nat.gcdA N p : ℤ) : A)) + ((p : A) * ((Nat.gcdB N p : ℤ) : A)) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hbez
    push_cast at this; exact this
  have hpnu : ¬ IsUnit (p : A) := by
    rw [ValuationSubring.valuation_eq_one_iff]
    have := (ValuationSubring.mem_nonunits_iff A).mp hpA
    push_cast; exact this.ne
  have hNu : IsUnit (N : A) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hbezA with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (isUnit_of_mul_isUnit_left h) hpnu
  have hvN : A.valuation (N : ℂ) = 1 := by
    have := (ValuationSubring.valuation_eq_one_iff A _).mp hNu
    push_cast at this; exact this

  have hsq : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h2 : A.valuation ((Real.sqrt N : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← map_pow, hsq, hvN]
  rcases lt_trichotomy (A.valuation ((Real.sqrt N : ℝ) : ℂ)) 1 with h | h | h
  · exact absurd h2 (pow_lt_one₀ zero_le' h two_ne_zero).ne
  · exact h
  · exact absurd h2 (one_lt_pow₀ h two_ne_zero).ne'

end GlobalTheory
