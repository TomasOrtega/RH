import Formalism.RealPlaceAnalysis.StatementA

open Finset

noncomputable section

namespace Formalism.REAL

/- English proof (translation)
Introduce `V _ _ X U B C hB hC hX j k`. Proceed by induction on `k generalizing j with`. Consider the case `zero => intro w _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `w hw`. Take `⟨hXw, hnorm⟩` from `hX j w hw`. Establish `h1` using `ih (j + 1) (X w) hXw`. Establish `e : B + ((j + 1 : ℕ) : ℝ) + (k : ℝ) = B + (j : ℝ) + ((k : ℝ) + 1)` using `by push_cast; ring`. Rewrite `h1` using `[e]`.

Rewrite using `[show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]`. Establish `hj : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hBj : 0 ≤ B + (j : ℝ)` using `by linarith`. Establish `hL : 0 ≤ B + (j : ℝ) + ((k : ℝ) + 1)` using `by linarith`.

Establish `hBjL : B + (j : ℝ) ≤ B + (j : ℝ) + ((k : ℝ) + 1)` using `by linarith`. Establish `hCk : 0 ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem iteratedGrowthBound_holds : GrowthIter := by
  intro V _ _ X U B C hB hC hX j k
  induction k generalizing j with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    obtain ⟨hXw, hnorm⟩ := hX j w hw
    have h1 := ih (j + 1) (X w) hXw
    have e : B + ((j + 1 : ℕ) : ℝ) + (k : ℝ) = B + (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
    rw [e] at h1
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hBj : 0 ≤ B + (j : ℝ) := by linarith
    have hL : 0 ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hBjL : B + (j : ℝ) ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hCk : 0 ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k := by positivity
    calc ‖(X ^ (k + 1)) w‖ = ‖(X ^ k) (X w)‖ := by rw [pow_succ, Module.End.mul_apply]
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * ‖X w‖ := h1
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * (C * (B + j) * ‖w‖) := by gcongr
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k *
            (C * (B + (j : ℝ) + ((k : ℝ) + 1)) * ‖w‖) := by gcongr
      _ = C ^ (k + 1) * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ (k + 1) * ‖w‖ := by ring

/- English proof (translation)
Introduce `C m t hC hm ht h`. Establish `hCt : 0 ≤ C * t` using `mul_nonneg hC ht`. Establish `hr0 : 0 ≤ C * t * Real.exp 1` using `by positivity`. Use `Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) ((summable_geometric_of_lt_one hr0 h).mul_left (Real.exp m))` and prove the remaining obligations. Establish `hx : 0 ≤ m + (k : ℝ)` using `by positivity`.

Establish `h1` using `Real.pow_div_factorial_le_exp (m + k) hx k`. Establish `h2 : Real.exp (m + k) = Real.exp m * Real.exp 1 ^ k`. Rewrite using `[Real.exp_add, ← Real.exp_nat_mul, mul_one]`. Establish `hCtk : 0 ≤ (C * t) ^ k` using `pow_nonneg hCt k`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem taylorSummable_holds : TaylorRadius := by
  intro C m t hC hm ht h
  have hCt : 0 ≤ C * t := mul_nonneg hC ht
  have hr0 : 0 ≤ C * t * Real.exp 1 := by positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 h).mul_left (Real.exp m))
  have hx : 0 ≤ m + (k : ℝ) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (m + k) hx k
  have h2 : Real.exp (m + k) = Real.exp m * Real.exp 1 ^ k := by
    rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
  have hCtk : 0 ≤ (C * t) ^ k := pow_nonneg hCt k
  calc (C * t) ^ k * (m + k) ^ k / (k.factorial : ℝ)
      = (C * t) ^ k * ((m + k) ^ k / (k.factorial : ℝ)) := by ring
    _ ≤ (C * t) ^ k * Real.exp (m + k) := by gcongr
    _ = Real.exp m * (C * t * Real.exp 1) ^ k := by rw [h2]; ring

end Formalism.REAL
