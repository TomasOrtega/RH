import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _))
    (fun n => ?_) ((Real.summable_nat_rpow.2 (by norm_num : (-(3 / 2) : ℝ) < -1)).mul_left 2)
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.log_le_rpow_div hx.le one_half_pos
  have key : (n : ℝ) ^ (-(3 / 2) : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hx]
    norm_num
  rw [key]
  calc Real.log n / (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem RestSummable.proof (hB : RestPBound.Statement) : RestSummable.Statement := by
  intro d S B0 F Q hQ
  obtain ⟨c, hc⟩ := hB d S.vol F Q hQ
  have hg : Summable (fun p : primesAbove S B0 =>
      |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2)) :=
    (summable_log_div_sq.subtype (primesAbove S B0)).mul_left |c|
  refine Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => ?_) hg
  have h := (hc p.1 (S.frob p.1) p.2.1).2
  calc |rest₂ d S.vol p (S.frob p) Q| ≤ c * Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2 := h
    _ ≤ |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self c)
          (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _))

end GroundTheory.Heights₂.Heights.TheoremB
