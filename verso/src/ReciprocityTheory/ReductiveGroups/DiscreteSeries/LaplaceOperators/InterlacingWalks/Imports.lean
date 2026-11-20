import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Introduce `n Q x s d N hx hstep`. Establish `key : ∀ m : ℕ, m ≤ N → Q (x + ((m : ℝ) * d) • Pi.single s 1)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _`.

Simplify using `using hx`. Consider the case `succ m ih`. Introduce `hm`. Establish `h` using `hstep m (by omega) (ih (by omega))`. Rewrite using `[Nat.cast_succ]`.

Conclude with `h`. Conclude with `key N le_rfl`.
-/
theorem seg : SegStatement := by
  intro n Q x s d N hx hstep
  have key : ∀ m : ℕ, m ≤ N → Q (x + ((m : ℝ) * d) • Pi.single s 1) := by
    intro m
    induction m with
    | zero => intro _; simpa using hx
    | succ m ih =>
      intro hm
      have h := hstep m (by omega) (ih (by omega))
      rw [Nat.cast_succ]
      exact h
  exact key N le_rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
