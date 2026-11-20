import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Use `push_cast`. Conclude with `le_trans (v.map_add _ _) (max_le ih (by simp))`.
-/
theorem valuation_nnreal_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans (v.map_add _ _) (max_le ih (by simp))

/- English proof (translation)
Consider the cases of `z with`. Consider the case `ofNat n => simpa using valuation_nnreal_natCast_le_one v n`. Consider the case `negSucc n`. Rewrite using `[Int.cast_negSucc, Valuation.map_neg]`. Conclude with `valuation_nnreal_natCast_le_one v (n + 1)` after adjusting the coercions.
-/
theorem valuation_nnreal_intCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (z : ℤ) : v (z : L) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_nnreal_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_nnreal_natCast_le_one v (n + 1)

/- English proof (translation)
Introduce `L _ v p l hp hlp`. Use `le_antisymm (valuation_nnreal_natCast_le_one v l) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p` using `Nat.gcd_eq_gcd_ab l p`.

Rewrite `hb` using `[hlp, Nat.cast_one]`. Establish `hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L)`. Use `congrArg (fun z : ℤ => (z : L)) hb` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `h1 : v (1 : L) < 1`. Rewrite using `[hL]`. Use `lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[v.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt`.

Rewrite using `[v.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp`. Simplify using `at h1`.
-/
theorem natCast_eq_one_of_coprime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  intro L _ v p l hp hlp
  refine le_antisymm (valuation_nnreal_natCast_le_one v l) ?_
  by_contra hlt
  push_neg at hlt
  have hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p := Nat.gcd_eq_gcd_ab l p
  rw [hlp, Nat.cast_one] at hb
  have hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L) := by
    have := congrArg (fun z : ℤ => (z : L)) hb
    push_cast at this
    exact this
  have h1 : v (1 : L) < 1 := by
    rw [hL]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp
  simp at h1

end GlobalTheory.AlmostEt
