import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.RatDenAwayP

/- English proof (translation)
Establish `h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ` using `h v`. Rewrite `h1` using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `h1`.
-/
theorem val_le_one (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) (v : AwayP p) :
    v.1.valuation ℚ q ≤ 1 := by
  have h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

def primeHOS (l : ℕ) (hl : l.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(l : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)}`. Introduce `e`. Establish `e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)}` using `e`. Rewrite `e'` using `[Ideal.span_singleton_eq_span_singleton]`.

Establish `h1 : l ∣ p` using `Int.natCast_dvd_natCast.1 e'.dvd`. Establish `h2 : p ∣ l` using `Int.natCast_dvd_natCast.1 e'.symm.dvd`. Conclude with `hne (Nat.dvd_antisymm h1 h2)`. Set `v : AwayP p` to `⟨primeHOS l hl, hv⟩`. Establish `hq` using `val_le_one p q h v`.

Establish `hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1`. Rewrite using `[valuation_lt_one_iff_mem]`. Use `show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}`. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `hd` after adjusting the coercions.

Establish `hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1`. Establish `e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ)`. Rewrite using `[algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]`. Rewrite using `[e, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `hnum` using `[valuation_lt_one_iff_mem]`. Express the relevant statement in the definitionally equal form `q.num ∈ Ideal.span {(l : ℤ)} at hnum`. Rewrite `hnum` using `[Ideal.mem_span_singleton, Int.natCast_dvd]`. Establish `hc : Nat.Coprime l q.den` using `Nat.Coprime.coprime_dvd_left hnum q.reduced`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hl).1 hc hd`.
-/
theorem prime_dvd_den (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ q.den) : l = p := by
  by_contra hne
  have hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro e
    have e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)} := e
    rw [Ideal.span_singleton_eq_span_singleton] at e'
    have h1 : l ∣ p := Int.natCast_dvd_natCast.1 e'.dvd
    have h2 : p ∣ l := Int.natCast_dvd_natCast.1 e'.symm.dvd
    exact hne (Nat.dvd_antisymm h1 h2)
  let v : AwayP p := ⟨primeHOS l hl, hv⟩
  have hq := val_le_one p q h v
  have hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1 := by
    rw [valuation_lt_one_iff_mem]
    show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}
    rw [Ideal.mem_span_singleton]; exact_mod_cast hd
  have hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1 := by
    have e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ) := by
      rw [algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    calc (primeHOS l hl).valuation ℚ q * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ))
        ≤ 1 * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) := by gcongr
      _ < 1 := by rw [one_mul]; exact hden
  rw [valuation_lt_one_iff_mem] at hnum
  change q.num ∈ Ideal.span {(l : ℤ)} at hnum
  rw [Ideal.mem_span_singleton, Int.natCast_dvd] at hnum
  have hc : Nat.Coprime l q.den := Nat.Coprime.coprime_dvd_left hnum q.reduced
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 hc hd

end GlobalTheory.RatDenAwayP

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ q h`. Establish `hden : q.den = p ^ q.den.primeFactorsList.length` using `Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)`. Use `⟨q.den.primeFactorsList.length, q.num, ?_⟩` and prove the remaining obligations. Rewrite using `[← hden]`. Conclude with `Rat.den_mul_eq_num q`.
-/
theorem ratDen_pow_of_intAfP : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p →
    ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  intro p _ q h
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hden]
  exact Rat.den_mul_eq_num q

end GlobalTheory
