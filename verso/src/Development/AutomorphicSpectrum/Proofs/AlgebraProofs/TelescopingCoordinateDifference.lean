import Mathlib

namespace GlobalTheory.CompanionTheory.Telescope

/- English proof (translation)
Use `set G : ℕ → ℝ := fun m => F (fun j => if (j : ℕ) < m then b j else a j) with hG`. Establish `h0 : G 0 = F a` using `by simp [hG]`. Establish `hn : G n = F b` using `by simp [hG]`. Rewrite using `[← h0, ← hn, ← Finset.sum_range_sub' G n, Finset.sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [hG, Nat.lt_succ_iff, Fin.lt_def, Fin.le_def]`.
-/
theorem telescope_fin_positions (α : Type) (n : ℕ) (F : (Fin n → α) → ℝ) (a b : Fin n → α) :
    F a - F b = ∑ i : Fin n, (F (fun j => if j < i then b j else a j) - F (fun j => if j ≤ i then b j else a j)) := by
  classical
  set G : ℕ → ℝ := fun m => F (fun j => if (j : ℕ) < m then b j else a j) with hG
  have h0 : G 0 = F a := by simp [hG]
  have hn : G n = F b := by simp [hG]
  rw [← h0, ← hn, ← Finset.sum_range_sub' G n, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hG, Nat.lt_succ_iff, Fin.lt_def, Fin.le_def]

end GlobalTheory.CompanionTheory.Telescope
