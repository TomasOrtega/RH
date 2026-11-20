import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/- English proof (translation)
Use `⟨fun F H => (hB F H).2.trans (hC F H), ?_⟩` and prove the remaining obligations. Establish `h` using `(hB Polynomial.X Polynomial.X).2.trans (hC Polynomial.X Polynomial.X)`. Simplify using `only [Polynomial.eval_X] at h`. Rewrite using `[h]`. Establish `hm : uniformMean (fun x : ℝ => x) = 0`.

Simplify using `[uniformMean, integral_id]`. Establish `hg : ∀ c : ℝ, centredPrimitive Polynomial.X c = (c ^ 2 - 1) / 2`. Introduce `c`. Simplify using `only [centredPrimitive, Polynomial.eval_X]`. Rewrite using `[hm]`.

Simplify using `only [sub_zero, integral_id]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : ∀ c : ℝ, centredPrimitive Polynomial.X c * centredPrimitive Polynomial.X c / (1 - c ^ 2) = (1 - c ^ 2) / 4`. Introduce `c`. Rewrite using `[hg]`.

Break down `eq_or_ne (1 - c ^ 2) 0 with h0 | h0` into its components or cases. Establish `: c ^ 2 - 1 = 0` using `by linarith`. Rewrite using `[h0, this]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hm]`. Simplify using `only [hq]`. Simplify using `[intervalIntegral.integral_div, integral_pow]`. Evaluate the numerical expressions.
-/
theorem ZonalBilinearFormula.proof (hB : ZonalHeightReduction.Statement)
    (hC : ZonalKernelPairing.Statement) : ZonalBilinearFormula.Statement := by
  refine ⟨fun F H => (hB F H).2.trans (hC F H), ?_⟩
  have h := (hB Polynomial.X Polynomial.X).2.trans (hC Polynomial.X Polynomial.X)
  simp only [Polynomial.eval_X] at h
  rw [h]
  have hm : uniformMean (fun x : ℝ => x) = 0 := by
    simp [uniformMean, integral_id]
  have hg : ∀ c : ℝ, centredPrimitive Polynomial.X c = (c ^ 2 - 1) / 2 := by
    intro c
    simp only [centredPrimitive, Polynomial.eval_X]
    rw [hm]
    simp only [sub_zero, integral_id]
    ring
  have hq : ∀ c : ℝ, centredPrimitive Polynomial.X c * centredPrimitive Polynomial.X c / (1 - c ^ 2)
      = (1 - c ^ 2) / 4 := by
    intro c
    rw [hg]
    rcases eq_or_ne (1 - c ^ 2) 0 with h0 | h0
    · have : c ^ 2 - 1 = 0 := by linarith
      rw [h0, this]; simp
    · field_simp
      ring
  rw [hm]
  simp only [hq]
  simp [intervalIntegral.integral_div, integral_pow]
  norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
