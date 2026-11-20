import Mathlib

namespace Bl.general_b_fact_right'''

/- English proof (translation)
Introduce `K _ _ p a b ha hb hab k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ (norm_nonneg _) ha`.

Use `_ = ‖a - b‖ := one_mul _`. Use `_ ≤ _ := hab`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem goal1 :
  ∀ {K : Type} [inst : NormedField.{0} K] [IsUltrametricDist.{0} K] {p : Nat} {a b : K},
  LE.le.{0} (Norm.norm.{0} a) 1 →
    LE.le.{0} (Norm.norm.{0} b) 1 →
      LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) (Inv.inv.{0} (Nat.cast.{0} p)) →
        ∀ (k : Nat),
          LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} a k) (HPow.hPow.{0, 0, 0} b k)))
            (Inv.inv.{0} (Nat.cast.{0} p)) := by
  intro K _ _ p a b ha hb hab k
  induction k with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      calc ‖a‖ ^ n * ‖a - b‖ ≤ 1 * ‖a - b‖ := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) ha
        _ = ‖a - b‖ := one_mul _
        _ ≤ _ := hab
    · rw [norm_mul]
      calc ‖a ^ n - b ^ n‖ * ‖b‖ ≤ ‖a ^ n - b ^ n‖ * 1 := by gcongr
        _ = ‖a ^ n - b ^ n‖ := mul_one _
        _ ≤ _ := ih

end Bl.general_b_fact_right'''
