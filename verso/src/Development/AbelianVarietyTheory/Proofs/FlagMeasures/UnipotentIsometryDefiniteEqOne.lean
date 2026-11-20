import Mathlib

open Matrix Finset Real

namespace GlobalTheory

open scoped ComplexOrder in

/- English proof (translation)
Introduce `n m A c hc hA hm`. Establish `hU : Aᴴ * A = 1`. Establish `h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`. Conclude with `smul_right_injective _ hc h1`.

Establish `hU' : A * Aᴴ = 1` using `mul_eq_one_comm.mp hU`. Establish `hcomm : Commute (A - 1)ᴴ (A - 1)` using `by show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU', one_mul, mul_one]`. Normalize the expressions using the abelian group laws. Establish `hN : (A - 1) ^ (m + 1) = 0` using `by rw [pow_succ, hm, zero_mul]`.

Establish `hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1)`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Establish `hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0`. Rewrite using `[hcomm.mul_pow, hN, mul_zero]`. Establish `key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro h`. Simplify using `using h`. Consider the case `succ k ih`.

Introduce `hk`. Apply `ih` to reduce the goal to its premises. Establish `h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0`. Rewrite using `[Matrix.conjTranspose_pow, hBh, ← pow_add, show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]`. Conclude with `Matrix.conjTranspose_mul_self_eq_zero.mp h2`.

Conclude with `sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))`.
-/
theorem unipotent_isometry_definite_eq_one :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), c ≠ 0 → Aᴴ * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * A = c • 1 → (A - 1) ^ m = 0 → A = 1 := by
  intro n m A c hc hA hm

  have hU : Aᴴ * A = 1 := by
    have h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_right_injective _ hc h1
  have hU' : A * Aᴴ = 1 := mul_eq_one_comm.mp hU

  have hcomm : Commute (A - 1)ᴴ (A - 1) := by
    show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU',
      one_mul, mul_one]
    abel
  have hN : (A - 1) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]

  have hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0 := by
    rw [hcomm.mul_pow, hN, mul_zero]
  have key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro hk
      apply ih
      have h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_pow, hBh, ← pow_add,
          show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))

end GlobalTheory
