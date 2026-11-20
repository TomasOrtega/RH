import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem BdEqHolo.proof : BdEqHolo.Statement := by
  intro X _ D A R j
  refine ⟨fun m v hv => ?_, fun y hy => ?_⟩
  · have h : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) v := (R.compat j m).1 v ⟨hv.1, hv.2.1⟩
    have hi : ∀ i, AnalyticAt ℂ (fun w => (R.ψ j ∘ (A.chart m).symm) w i) v :=
      (analyticAt_pi_iff (f := fun i w => (R.ψ j ∘ (A.chart m).symm) w i)).1 h
    show AnalyticAt ℂ (fun w => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart m).symm) w i) v
    exact Finset.analyticAt_fun_prod _ fun i _ => hi i
  · have hmem := R.mem_Yo_iff j (R.ψ j y) hy.2
    rw [(R.ψ j).left_inv hy.1] at hmem
    rw [hmem, not_not]
    simp only [bdEq, Finset.prod_eq_zero_iff, coordDiv, Set.mem_ofPred_eq]

end GroundTheory.Heights₂.Heights.AnalyticLimit
