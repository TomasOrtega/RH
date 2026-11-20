import Mathlib

namespace PositivityTheory.PrwZar

/- English proof (translation)
Take `⟨a, b, c, d, h⟩` from `Nat.sum_four_squares n`. Establish `hn : (n : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2`. Rewrite using `[← h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩ <;>`. Rewrite using `[hn]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring`.
-/
theorem exists_quat (n : ℕ) : ∃ α : Matrix (Fin 4) (Fin 4) ℤ,
    α.transpose * α = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    α * α.transpose = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  have hn : (n : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]
    push_cast
    ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩ <;>
  · rw [hn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

end PositivityTheory.PrwZar
