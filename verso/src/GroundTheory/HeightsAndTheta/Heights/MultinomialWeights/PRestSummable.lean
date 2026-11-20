import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open Finset

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun n => div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)) (fun n => ?_) ((Real.summable_nat_rpow.2 (by norm_num : (-(3 / 2) : ℝ) < -1)).mul_left 2)` and prove the remaining obligations. Break down `n.eq_zero_or_pos with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hx : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `h1` using `Real.log_le_rpow_div hx.le one_half_pos`.

Establish `key : (n : ℝ) ^ (-(3 / 2) : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2`. Rewrite using `[← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hx]`. Evaluate the numerical expressions. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation.
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
Introduce `d S B0 F Q hQ`. Take `⟨c, hc⟩` from `hB d S.vol F Q hQ`. Establish `hg : Summable (fun p : primesAbove S B0 => |c| * (Real.log (p : ℕ) / (((p : ℕ) : ℝ)) ^ 2))` using `(summable_log_div_sq.subtype (primesAbove S B0)).mul_left |c|`. Use `Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => ?_) hg` and prove the remaining obligations. Establish `h` using `(hc p.1 (S.frob p.1) p.2.1).2`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self c) (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _))`.
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
