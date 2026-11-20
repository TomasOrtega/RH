import Mathlib
import Formalism.PeriodIntegrals.SmithMat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmithNormalForm.ExistsMoveRow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem smith_normal_form_theory.{u} : PI.SmithMat.{u} := by
  intro R _ _ _ n A
  obtain ⟨d, ⟨U, V, hU, hV, h⟩, hd⟩ := PI.SmithWork.smith n A
  exact ⟨U, V, d, hU, hV, h, hd⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem smith_diagonal_entries.{u} : PI.SmithDiag.{u} := by
  intro R _ _ _ n A
  obtain ⟨U, V, d, hU, hV, h, -⟩ := smith_normal_form_theory R n A
  exact ⟨U, V, d, hU, hV, h⟩
