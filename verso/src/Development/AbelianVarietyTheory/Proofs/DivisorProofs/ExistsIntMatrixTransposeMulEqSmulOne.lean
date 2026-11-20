import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨a, b, c, d, h⟩` from `Nat.sum_four_squares s`. Establish `h' : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (s : ℤ)`. Conclude with `h` after adjusting the coercions. Use `⟨!![(a:ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`.

Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>`. Apply the tactic sequence `first | linear_combination h' | ring`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>`. Apply the tactic sequence `first | linear_combination h' | ring`.
-/
theorem exists_int_matrix_transpose_mul_eq_smul_one (s : ℕ) :
    ∃ x : Matrix (Fin 4) (Fin 4) ℤ, x.transpose * x = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
      x * x.transpose = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares s
  have h' : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (s : ℤ) := by
    exact_mod_cast h
  refine ⟨!![(a:ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
      first | linear_combination h' | ring

end GlobalTheory
