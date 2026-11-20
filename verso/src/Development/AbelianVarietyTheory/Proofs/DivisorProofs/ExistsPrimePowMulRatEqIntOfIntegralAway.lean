import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open IsDedekindDomain

/- English proof (translation)
Introduce `p hp q h`. Establish `hp' : p.Prime` using `hp.out`. Establish `key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p`. Introduce `l hl hld`. Assume the negation of the conclusion as `hne`.

Establish `hlI : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 hl`. Set `v : HeightOneSpectrum ℤ` to `⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩`. Establish `hv : v.asIdeal ≠ Ideal.span {(p : ℤ)}`. Introduce `e`. Establish `h1 : (l : ℤ) ∣ (p : ℤ)` using `Ideal.mem_span_singleton.1 (by`.

Establish `: (p : ℤ) ∈ Ideal.span {(p : ℤ)}` using `Ideal.mem_span_singleton_self _`. Rewrite `this` using `[← e]`. Conclude with `Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by`. Conclude with `Ideal.mem_span_singleton.2 ⟨c, hc⟩))`. Establish `h2 : l ∣ p` using `Int.natCast_dvd_natCast.1 h1`.

Conclude with `hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)`. Establish `hq` using `h ⟨v, hv⟩`. Rewrite `hq` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hq2 : v.valuation ℚ q ≤ 1`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `hq`. Establish `hb : ((q.den : ℤ)) ≠ 0` using `by exact_mod_cast q.den_nz`. Establish `hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal`. Introduce `hd hn`. Establish `hd' : (l : ℤ) ∣ (q.den : ℤ)` using `Ideal.mem_span_singleton.1 hd`.

Establish `hn' : (l : ℤ) ∣ q.num` using `Ideal.mem_span_singleton.1 hn`. Establish `hc : IsCoprime q.num (q.den : ℤ)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Conclude with `q.reduced` after adjusting the coercions. Conclude with `hlI.not_unit (hc.isUnit_of_dvd' hn' hd')`.

Establish `e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ)))`. Simplify using `[Rat.num_div_den]`. Rewrite `hq2` using `[e, v.valuation_div_le_one_iff ℚ q.num hb hcop]`. Conclude with `hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))`. Establish `hden : q.den = p ^ q.den.primeFactorsList.length` using `Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)`.

Use `⟨q.den.primeFactorsList.length, q.num, ?_⟩` and prove the remaining obligations. Establish `: ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ)` using `by conv_rhs => rw [hden] push_cast; rfl`. Rewrite using `[this, Rat.den_mul_eq_num]`.
-/
theorem ratint_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ),
    (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) →
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  intro p hp q h
  have hp' : p.Prime := hp.out
  have key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p := by
    intro l hl hld
    by_contra hne
    have hlI : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    let v : HeightOneSpectrum ℤ :=
      ⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro e
      have h1 : (l : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (by
        have : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
        rw [← e] at this
        exact Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by
          exact Ideal.mem_span_singleton.2 ⟨c, hc⟩))
      have h2 : l ∣ p := Int.natCast_dvd_natCast.1 h1
      exact hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)
    have hq := h ⟨v, hv⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hq
    have hq2 : v.valuation ℚ q ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hq
    have hb : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
    have hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal := by
      intro hd hn
      have hd' : (l : ℤ) ∣ (q.den : ℤ) := Ideal.mem_span_singleton.1 hd
      have hn' : (l : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 hn
      have hc : IsCoprime q.num (q.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast q.reduced
      exact hlI.not_unit (hc.isUnit_of_dvd' hn' hd')
    have e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ))) := by
      simp [Rat.num_div_den]
    rw [e, v.valuation_div_le_one_iff ℚ q.num hb hcop] at hq2
    exact hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have : ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.den_mul_eq_num]

end GlobalTheory
