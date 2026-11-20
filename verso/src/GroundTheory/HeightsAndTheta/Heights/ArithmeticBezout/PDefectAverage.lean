import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem IsChowFormCycle.ne_zero {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem DefectAverage.proof (h1 : MahlerAverageSplit.Statement) (h2 : CycleAverage.Statement) :
    DefectAverage.Statement := by
  intro n e δ h Z f hZ
  obtain ⟨hi1, hm1⟩ := h1 n e δ h f hZ.chow.ne_zero hZ.homog
  obtain ⟨hi2, hm2⟩ := h2 n e δ h Z f hZ
  have hi : IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) := by
    unfold mahlerDefect; exact hi1.sub hi2
  refine ⟨hi, ?_⟩
  have hsub : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) =
      (⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))) -
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) := by
    simp only [setAverage_eq, mahlerDefect]
    rw [integral_sub hi1 hi2, smul_sub]
  rw [hsub, ← hm1, hm2]
  ring

end GroundTheory.Heights₂.Heights
