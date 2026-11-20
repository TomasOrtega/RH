import Mathlib

/- English proof (translation)
Introduce `Ω _ A a b ha hb hab m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n` using `by ring`.

Rewrite using `[hsplit]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih`. Rewrite using `[map_mul, map_pow]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab`.
-/
theorem UpperTheory.Reformulated.B.Qh11.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
