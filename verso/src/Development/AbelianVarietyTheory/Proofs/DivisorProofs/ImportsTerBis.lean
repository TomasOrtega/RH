import Mathlib

namespace GlobalTheory.IntertwiningOperators

open Polynomial

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C c`. Simplify using `only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]`. Consider the case `add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]`. Consider the case `monomial n c ih`.

Rewrite using `[pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X, map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]`.
-/
theorem intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X,
      map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/- English proof (translation)
Introduce `K _ a b A B C hcop h`. Take `⟨u, v, huv⟩` from `hcop`. Establish `h1 : aeval B u * aeval B (Matrix.charpoly A) = 1`. Use `congrArg (aeval B) huv` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one]`.

Conclude with `this`. Establish `h2 : aeval B (Matrix.charpoly A) * C = 0`. Rewrite using `[intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) := by
  intro K _ a b A B C hcop h
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B u * aeval B (Matrix.charpoly A) = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact this
  have h2 : aeval B (Matrix.charpoly A) * C = 0 := by
    rw [intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = (aeval B u * aeval B (Matrix.charpoly A)) * C := by rw [h1, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]

end GlobalTheory.IntertwiningOperators
