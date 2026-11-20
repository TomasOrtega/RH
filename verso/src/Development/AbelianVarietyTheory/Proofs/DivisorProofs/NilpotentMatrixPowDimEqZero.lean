import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `d X hX`. Establish `h` using `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hX`. Establish `h0 : X.charpoly = Polynomial.X ^ Fintype.card (Fin d)` using `sub_eq_zero.mp (IsNilpotent.eq_zero h)`. Establish `hc` using `Matrix.aeval_self_charpoly X`. Rewrite `hc` using `[h0]`.

Simplify using `using hc`.
-/
theorem matrix_pow_dim_eq_zero_of_isNilpotent :
    ∀ (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ), IsNilpotent X → X ^ d = 0 := by
  intro d X hX
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hX
  have h0 : X.charpoly = Polynomial.X ^ Fintype.card (Fin d) :=
    sub_eq_zero.mp (IsNilpotent.eq_zero h)
  have hc := Matrix.aeval_self_charpoly X
  rw [h0] at hc
  simpa using hc

end GlobalTheory
