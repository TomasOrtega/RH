import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
theorem dualWeylModuleRowActionStable : DualWeylRowStable := by
  intro R _ r n ν g f hf
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hw, hc⟩ := hf
  refine ⟨isWH_algHom (rowAct R g) (colW r n) (colW r n)
    (rowAct_X_isWH g) hw, ?_⟩
  intro l j hlj
  rw [colAddGen_rowAct, rename_rowAct, hc l j hlj]

end Formalism.GradedWeylDivisibility
