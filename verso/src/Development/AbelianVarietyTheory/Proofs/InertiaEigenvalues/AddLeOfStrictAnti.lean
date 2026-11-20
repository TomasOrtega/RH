import Mathlib

namespace GlobalTheory.StrictAntiAddLe

/- English proof (translation)
Introduce `m s hs k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j h`. Establish `hij : j = i` using `Fin.ext (by simpa using h)`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `i j h`. Establish `hj` using `j.isLt`.

Establish `hlt : (i : ℕ) + k < m` using `by omega`. Establish `h1` using `ih i ⟨(i : ℕ) + k, hlt⟩ rfl`. Establish `h2 : s j < s ⟨(i : ℕ) + k, hlt⟩`. Apply `hs` to reduce the goal to its premises. Rewrite using `[Fin.lt_def]`.

Use `show (i : ℕ) + k < (j : ℕ)`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem add_le_of_strictAnti : ∀ {m : ℕ} {s : Fin m → ℕ}, StrictAnti s →
    ∀ (k : ℕ) (i j : Fin m), (↑j : ℕ) = (↑i : ℕ) + k → s j + k ≤ s i := by
  intro m s hs k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hlt : (i : ℕ) + k < m := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hlt⟩ rfl
    have h2 : s j < s ⟨(i : ℕ) + k, hlt⟩ := by
      apply hs
      rw [Fin.lt_def]
      show (i : ℕ) + k < (j : ℕ)
      omega
    omega

end GlobalTheory.StrictAntiAddLe
