import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset

namespace GlobalTheory

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

/- English proof (translation)
Unfold `inPart outPart`. Rewrite using `[Finset.prod_filter, Finset.prod_filter, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hm.ne']`. Rewrite using `[Finsupp.prod, Nat.support_factorization]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_mul]`. Break down `Nat.even_or_odd' (m.factorization p) with ⟨k, hk | hk⟩` into its components or cases. Establish `h1 : ¬ Odd (m.factorization p)`. Rewrite using `[hk]`. Simplify using the standard rewrite rules.

Establish `h2 : m.factorization p / 2 * 2 = m.factorization p` using `by omega`. Rewrite using `[if_neg (fun h => h1 h.2), if_neg (fun h => h1 h.2), h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : Odd (m.factorization p)` using `⟨k, hk⟩`. Establish `h2 : m.factorization p = m.factorization p / 2 * 2 + 1` using `by omega`.

Distinguish the cases in `hp : p ∣ m₀`. Rewrite using `[if_pos ⟨hp, h1⟩, if_neg (fun h => h.1 hp)] conv_rhs => rw [h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h => hp h.1), if_pos ⟨hp, h1⟩] conv_rhs => rw [h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inPart_mul_outPart_mul_sq (m₀ m : ℕ) (hm : 0 < m) :
    inPart m₀ m * outPart m₀ m * (∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)) ^ 2 = m := by
  unfold inPart outPart
  rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hm.ne']
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul]
  rcases Nat.even_or_odd' (m.factorization p) with ⟨k, hk | hk⟩
  · have h1 : ¬ Odd (m.factorization p) := by
      rw [hk]; simp
    have h2 : m.factorization p / 2 * 2 = m.factorization p := by omega
    rw [if_neg (fun h => h1 h.2), if_neg (fun h => h1 h.2), h2]
    ring
  · have h1 : Odd (m.factorization p) := ⟨k, hk⟩
    have h2 : m.factorization p = m.factorization p / 2 * 2 + 1 := by omega
    by_cases hp : p ∣ m₀
    · rw [if_pos ⟨hp, h1⟩, if_neg (fun h => h.1 hp)]
      conv_rhs => rw [h2]
      ring
    · rw [if_neg (fun h => hp h.1), if_pos ⟨hp, h1⟩]
      conv_rhs => rw [h2]
      ring

/- English proof (translation)
Introduce `m₀ m q hm hq`. Establish `h` using `inPart_mul_outPart_mul_sq m₀ m hm`. Use `set t := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2) with ht`. Establish `htm : t ∣ m`. Use `Dvd.intro_left (inPart m₀ m * outPart m₀ m * t) ?_` and prove the remaining obligations.

Use `Eq.trans ?_ h` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `htq : Nat.Coprime t q` using `Nat.Coprime.coprime_dvd_left htm hq`. Establish `hsq : jacobiSym ((t : ℤ) ^ 2) q = 1` using `jacobiSym.sq_one' (by simpa using htq)`. Establish `hz : (m : ℤ) = (inPart m₀ m : ℤ) * (outPart m₀ m : ℤ) * (t : ℤ) ^ 2` using `by exact_mod_cast h.symm`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem jacobiInOut : Formalism.HermitianLattices.GL2a2.JacobiInOut := by
  intro m₀ m q hm hq
  have h := inPart_mul_outPart_mul_sq m₀ m hm
  set t := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2) with ht
  have htm : t ∣ m := by
    refine Dvd.intro_left (inPart m₀ m * outPart m₀ m * t) ?_
    refine Eq.trans ?_ h
    ring
  have htq : Nat.Coprime t q := Nat.Coprime.coprime_dvd_left htm hq
  have hsq : jacobiSym ((t : ℤ) ^ 2) q = 1 := jacobiSym.sq_one' (by simpa using htq)
  have hz : (m : ℤ) = (inPart m₀ m : ℤ) * (outPart m₀ m : ℤ) * (t : ℤ) ^ 2 := by exact_mod_cast h.symm
  calc jacobiSym (m : ℤ) q
      = jacobiSym ((inPart m₀ m : ℤ) * (outPart m₀ m : ℤ) * (t : ℤ) ^ 2) q := by rw [← hz]
    _ = _ := by rw [jacobiSym.mul_left, jacobiSym.mul_left, hsq, mul_one]

end GlobalTheory
