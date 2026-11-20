import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cycleIntegral_eq_sum {n : ℕ} (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) :
    cycleIntegral h Z e g = Z.sum (fun W m => (m : ℝ) * coneIntegral h W e g) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CycleIntegralSection.proof : CycleIntegralSection.Statement := by
  intro n h Z u e g
  rw [cycleIntegral_eq_sum, cycleSection,
    ← Finsupp.sum_finsetSum_index (by intro W; simp) (by intro W a b; push_cast; ring)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.sum_smul_index' (by intro W'; simp), cycleIntegral_eq_sum, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun W' _ => ?_
  simp only [smul_eq_mul, Nat.cast_mul]
  ring

end

end GroundTheory.Heights₂.Heights
