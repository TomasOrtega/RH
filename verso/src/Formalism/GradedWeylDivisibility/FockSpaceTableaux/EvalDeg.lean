import Formalism.GradedWeylDivisibility.StatementC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCdegLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `B _ τ _ x y c _ _ _ p`. Apply `lcdeg_degreeOf_aeval_le` to reduce the goal to its premises. Introduce `m hm`. Establish `hf : ∀ v, degreeOf c ((fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v) v) ≤ (if v = y then 1 else 0) + (if v = c then 1 else 0)`. Introduce `v`.

Distinguish the cases in `hvx : v = x`. Substitute `hvx` using the available equality. Simplify using `only [if_true]`. Establish `h1 : degreeOf c (1 : MvPolynomial τ B) = 0` using `by rw [← C_1, degreeOf_C]`. Rewrite using `[h1]`.

Conclude with `Nat.zero_le _`. Distinguish the cases in `hvy : v = y`. Substitute `hvy` using the available equality. Simplify using `only [hvx, if_false, if_true, degreeOf_neg]`. Establish `h2` using `lcdeg_degreeOf_X_le (R := B) c c`.

Simplify using `only [if_true] at h2`. Use linear arithmetic over natural numbers and integers. Simplify using `only [hvx, hvy, if_false, zero_add]`. Conclude with `lcdeg_degreeOf_X_le (R := B) c v`. Use `le_trans (Finset.sum_le_sum (g := fun v => m v * (if v = y then 1 else 0) + m v * (if v = c then 1 else 0)) fun v _ => ?_) ?_` and prove the remaining obligations.

Rewrite using `[← Nat.mul_add]`. Conclude with `Nat.mul_le_mul_left _ (hf v)`. Rewrite using `[Finset.sum_add_distrib]`. Simplify using `only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]`. Establish `hy` using `monomial_le_degreeOf y hm`.

Establish `hc` using `monomial_le_degreeOf c hm`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem evalDegree : EvalDeg := by
  intro B _ τ _ x y c _ _ _ p
  apply lcdeg_degreeOf_aeval_le
  intro m hm
  have hf : ∀ v, degreeOf c ((fun v : τ => if v = x then (1 : MvPolynomial τ B)
      else if v = y then -X c else X v) v) ≤ (if v = y then 1 else 0) + (if v = c then 1 else 0) := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      simp only [if_true]
      have h1 : degreeOf c (1 : MvPolynomial τ B) = 0 := by rw [← C_1, degreeOf_C]
      rw [h1]
      exact Nat.zero_le _
    · by_cases hvy : v = y
      · subst hvy
        simp only [hvx, if_false, if_true, degreeOf_neg]
        have h2 := lcdeg_degreeOf_X_le (R := B) c c
        simp only [if_true] at h2
        omega
      · simp only [hvx, hvy, if_false, zero_add]
        exact lcdeg_degreeOf_X_le (R := B) c v
  refine le_trans (Finset.sum_le_sum (g := fun v => m v * (if v = y then 1 else 0) +
    m v * (if v = c then 1 else 0)) fun v _ => ?_) ?_
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hf v)
  · rw [Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hy := monomial_le_degreeOf y hm
    have hc := monomial_le_degreeOf c hm
    split_ifs <;> omega

end Formalism.GradedWeylDivisibility
