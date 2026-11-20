import Mathlib

namespace GlobalTheory.IntertwinerCoprimeCharpoly

open Polynomial

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]`.
-/
theorem pow_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (n : ℕ) :
    C * A ^ n = B ^ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]`. Consider the case `monomial n c`. Simplify using `only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, pow_intertwine A B C h n]`.
-/
theorem aeval_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_intertwine A B C h n]

/- English proof (translation)
Take `⟨u, v, huv⟩` from `hcop`. Establish `h1 : aeval B (u * A.charpoly + v * B.charpoly) = 1` using `by rw [huv, map_one]`. Rewrite `h1` using `[map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero]`. Establish `h2 : aeval B A.charpoly * C = 0`. Rewrite using `[← aeval_intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_intertwine_of_isCoprime_charpoly {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hcop : IsCoprime (Matrix.charpoly A) (Matrix.charpoly B)) (h : C * A = B * C) :
    C = (0 : Matrix (Fin b) (Fin a) K) := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B (u * A.charpoly + v * B.charpoly) = 1 := by rw [huv, map_one]
  rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero] at h1
  have h2 : aeval B A.charpoly * C = 0 := by
    rw [← aeval_intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = 1 * C := (Matrix.one_mul C).symm
    _ = (aeval B u * aeval B A.charpoly) * C := by rw [h1]
    _ = aeval B u * (aeval B A.charpoly * C) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h2, Matrix.mul_zero]

/- English proof (translation)
Introduce `A B C hcop h` and use `eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h`.
-/
theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) :=
  fun A B C hcop h => eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h

end GlobalTheory.IntertwinerCoprimeCharpoly
