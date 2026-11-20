import Mathlib

/- English proof (translation)
Introduce `r d hd k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j h`. Establish `hij : j = i` using `Fin.ext (by simpa using h)`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `i j h`. Establish `hj` using `j.isLt`.

Establish `hm : (i : ℕ) + k < r` using `by omega`. Establish `h1` using `ih i ⟨(i : ℕ) + k, hm⟩ rfl`. Establish `h2 : d j < d ⟨(i : ℕ) + k, hm⟩` using `hd (by`. Rewrite using `[Fin.lt_def]`. Simplify using `only`.

Use the proof step `omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Reformulated.B.Yoa4.add_gap_le :
    ∀ {r : ℕ} {d : Fin r → ℕ}, StrictAnti d → ∀ (k : ℕ) (i j : Fin r), (↑j : ℕ) = (↑i : ℕ) + k → d j + k ≤ d i := by
  intro r d hd k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hm : (i : ℕ) + k < r := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hm⟩ rfl
    have h2 : d j < d ⟨(i : ℕ) + k, hm⟩ := hd (by
      rw [Fin.lt_def]
      simp only
      omega)
    omega
