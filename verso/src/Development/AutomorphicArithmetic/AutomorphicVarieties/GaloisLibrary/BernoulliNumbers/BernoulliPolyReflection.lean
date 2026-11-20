import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

open Finset UpperTheory.V.Bern

/- English proof (translation)
Conclude with `Polynomial.bernoulli_eval_one_sub k x`.
-/
private theorem bernoulli_poly_reflection (k : ℕ) (x : ℚ) :
    (Polynomial.bernoulli k).eval (1 - x) = (-1) ^ k * (Polynomial.bernoulli k).eval x := by
  exact Polynomial.bernoulli_eval_one_sub k x

/- English proof (translation)
Introduce `N k a hN`. Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `bcoef`. Establish `e : ((a + N : ℕ) : ℚ) / N = 1 + (a : ℚ) / N` using `by push_cast; field_simp; ring`.

Rewrite using `[e, Polynomial.bernoulli_eval_one_add, mul_add]`. Use `congr 1`. Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Establish `: ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ)` using `by push_cast; ring`.

Rewrite using `[this, zpow_natCast, Nat.add_sub_cancel, div_pow]`. Clear the denominators using the available nonvanishing facts. Introduce `m hm`. Establish `hm' : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Unfold `bcoef`.

Establish `e : ((m * a : ℕ) : ℚ) / ((m * N : ℕ) : ℚ) = (a : ℚ) / N` using `by push_cast; field_simp`. Rewrite using `[e, Nat.cast_mul, mul_zpow, mul_assoc]`. Introduce `h`. Unfold `bcoef`. Establish `e : ((N - a : ℕ) : ℚ) / N = 1 - (a : ℚ) / N`.

Rewrite using `[Nat.cast_sub h]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, bernoulli_poly_reflection]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Bern.b_shift :
    ∀ (N k a : ℕ), 0 < N → bcoef N k (a + N) = bcoef N k a + (k : ℚ) * (a : ℚ) ^ (k - 1) ∧ (∀ m : ℕ, 0 < m → bcoef (m * N) k (m * a) = (m : ℚ) ^ ((k : ℤ) - 1) * bcoef N k a) ∧ (a ≤ N → bcoef N k (N - a) = (-1) ^ k * bcoef N k a) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold bcoef
    have e : ((a + N : ℕ) : ℚ) / N = 1 + (a : ℚ) / N := by
      push_cast; field_simp; ring
    rw [e, Polynomial.bernoulli_eval_one_add, mul_add]
    congr 1
    rcases k with _ | k
    · simp
    · have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this, zpow_natCast, Nat.add_sub_cancel, div_pow]
      field_simp
  · intro m hm
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold bcoef
    have e : ((m * a : ℕ) : ℚ) / ((m * N : ℕ) : ℚ) = (a : ℚ) / N := by
      push_cast; field_simp
    rw [e, Nat.cast_mul, mul_zpow, mul_assoc]
  · intro h
    unfold bcoef
    have e : ((N - a : ℕ) : ℚ) / N = 1 - (a : ℚ) / N := by
      rw [Nat.cast_sub h]; field_simp
    rw [e, bernoulli_poly_reflection]
    ring
