import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

namespace GlobalTheory

/- English proof (translation)
Introduce `C hC`. Establish `hC0 : 0 < C` using `by linarith`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hlC : 0 ≤ Real.log C` using `Real.log_nonneg hC`. Use `⟨2 * C + (2 + C + C * Real.log C) / Real.log 2, ?_⟩` and prove the remaining obligations.

Introduce `B s x h hB hs hs1 hx hh`. Establish `hy : 0 < 2 + C + x` using `by linarith`. Establish `hB0 : 0 < B` using `by linarith`. Establish `hL : Real.log (B / s) = Real.log B - Real.log s` using `Real.log_div hB0.ne' hs.ne'`. Establish `hlogs : Real.log s ≤ 0` using `Real.log_nonpos hs.le hs1`.

Establish `hlogB : Real.log 2 ≤ Real.log B` using `Real.log_le_log (by norm_num) hB`. Establish `hL2 : Real.log 2 ≤ Real.log (B / s)` using `by linarith`. Establish `h1 : Real.log ((2 + C + x) * s / C) ≤ (2 + C + x) * s / C - 1` using `Real.log_le_sub_one_of_pos (by positivity)`. Rewrite `h1` using `[Real.log_div (by positivity) hC0.ne', Real.log_mul hy.ne' hs.ne']`. Establish `h2 : C * (Real.log (2 + C + x) + Real.log s - Real.log C) ≤ (2 + C + x) * s - C`.

Combine the equalities or inequalities in the displayed calculation. Establish `hK : 0 ≤ 2 + C + C * Real.log C` using `by positivity`. Establish `h3 : 2 + C + C * Real.log C ≤ (2 + C + C * Real.log C) / Real.log 2 * Real.log (B / s)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : C * (-Real.log s) ≤ C * Real.log (B / s)` using `mul_le_mul_of_nonneg_left (by linarith) hC0.le`.

Establish `h5 : (2 + C) * s ≤ 2 + C` using `mul_le_of_le_one_right (by linarith) hs1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem boundary_lower_bound_numerical :
    ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, ∀ B s x h : ℝ, 2 ≤ B → 0 < s → s ≤ 1 → -C ≤ x →
      s * x - C * Real.log (2 + C + x) - C * Real.log (B / s) - C ≤ h →
      -(C' * Real.log (B / s)) ≤ h := by
  intro C hC
  have hC0 : 0 < C := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨2 * C + (2 + C + C * Real.log C) / Real.log 2, ?_⟩
  intro B s x h hB hs hs1 hx hh
  have hy : 0 < 2 + C + x := by linarith
  have hB0 : 0 < B := by linarith
  have hL : Real.log (B / s) = Real.log B - Real.log s := Real.log_div hB0.ne' hs.ne'
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hL2 : Real.log 2 ≤ Real.log (B / s) := by linarith
  have h1 : Real.log ((2 + C + x) * s / C) ≤ (2 + C + x) * s / C - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hC0.ne', Real.log_mul hy.ne' hs.ne'] at h1
  have h2 : C * (Real.log (2 + C + x) + Real.log s - Real.log C) ≤ (2 + C + x) * s - C := by
    calc _ ≤ C * ((2 + C + x) * s / C - 1) := mul_le_mul_of_nonneg_left h1 hC0.le
      _ = _ := by field_simp
  have hK : 0 ≤ 2 + C + C * Real.log C := by positivity
  have h3 : 2 + C + C * Real.log C ≤
      (2 + C + C * Real.log C) / Real.log 2 * Real.log (B / s) := by
    calc _ = (2 + C + C * Real.log C) / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h4 : C * (-Real.log s) ≤ C * Real.log (B / s) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0.le
  have h5 : (2 + C) * s ≤ 2 + C := mul_le_of_le_one_right (by linarith) hs1
  nlinarith

end GlobalTheory
