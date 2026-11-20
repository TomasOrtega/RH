import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

open CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.Forms

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dWedge_exists : CrystallineSemistableComparison.Onto.DWedge := by
  intro K A _ _ _ a f
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    ((exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).curryLeft (KaehlerDifferential.D K A f)), ?_⟩
  intro g₀ g
  unfold CrystallineSemistableComparison.Onto.form
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  congr 2
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

end GlobalTheory.CompanionTheory.Forms
