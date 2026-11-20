import Mathlib

/- English proof (translation)
Introduce `l f hf a`. Proceed by induction on `a with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← ih]`.

Establish `h1` using `Finset.sum_range_succ (fun k => f (n + k)) l`. Establish `h2` using `Finset.sum_range_succ' (fun k => f (n + k)) l`. Establish `h3 : f (n + l) = f n` using `hf n`. Establish `h4 : ∑ k ∈ Finset.range l, f (n + 1 + k) = ∑ k ∈ Finset.range l, f (n + (k + 1))` using `Finset.sum_congr rfl (fun k _ => by rw [add_assoc, add_comm 1 k])`. Simplify using `only [add_zero] at h2`.

Rewrite using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.Reformulated.B.DYdd7.main :
    ∀ {l : ℕ} (f : ℕ → ℚ),
      (∀ (k : ℕ), f (k + l) = f k) → ∀ (a : ℕ), ∑ k ∈ Finset.range l, f (a + k) = ∑ k ∈ Finset.range l, f k := by
  intro l f hf a
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun k => f (n + k)) l
    have h2 := Finset.sum_range_succ' (fun k => f (n + k)) l
    have h3 : f (n + l) = f n := hf n
    have h4 : ∑ k ∈ Finset.range l, f (n + 1 + k) = ∑ k ∈ Finset.range l, f (n + (k + 1)) :=
      Finset.sum_congr rfl (fun k _ => by rw [add_assoc, add_comm 1 k])
    simp only [add_zero] at h2
    rw [h4]
    linarith
