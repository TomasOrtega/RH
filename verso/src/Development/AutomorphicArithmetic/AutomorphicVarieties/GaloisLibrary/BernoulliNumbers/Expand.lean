import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `N k a hN`. Establish `hN' : (N : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Simplify using `only [bcoef]`. Rewrite using `[Polynomial.bernoulli, Polynomial.eval_finset_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hjk : j ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Rewrite using `[Polynomial.eval_monomial, div_pow]`. Establish `hsplit : (N : ℚ) ^ ((k : ℤ) - 1) = (N : ℚ) ^ ((j : ℤ) - 1) * (N : ℚ) ^ ((k - j : ℕ) : ℤ)`. Rewrite using `[← zpow_add₀ hN']`. Use `congr 1`.

Move the coercions through the operations in `[hjk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, zpow_natCast]`. Establish `hp : (N : ℚ) ^ (k - j) ≠ 0` using `pow_ne_zero _ hN'`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.V.Bern.b_expand :
    ∀ (N k a : ℕ), 0 < N → bcoef N k a = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * bernoulli j * (N : ℚ) ^ ((j : ℤ) - 1) * (a : ℚ) ^ (k - j) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [bcoef]
  rw [Polynomial.bernoulli, Polynomial.eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Polynomial.eval_monomial, div_pow]
  have hsplit : (N : ℚ) ^ ((k : ℤ) - 1) = (N : ℚ) ^ ((j : ℤ) - 1) * (N : ℚ) ^ ((k - j : ℕ) : ℤ) := by
    rw [← zpow_add₀ hN']
    congr 1
    push_cast [hjk]
    ring
  rw [hsplit, zpow_natCast]
  have hp : (N : ℚ) ^ (k - j) ≠ 0 := pow_ne_zero _ hN'
  field_simp
