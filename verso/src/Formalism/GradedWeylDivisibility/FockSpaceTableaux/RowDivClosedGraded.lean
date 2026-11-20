import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem row_divided_closed_graded : RowDivClosedGraded := by
  intro r n M hM f hf μ
  obtain ⟨h, hhM, hh⟩ := lgraded_multi M hM μ Finset.univ f hf
  convert hhM using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hh]
  congr 1
  apply propext
  constructor
  · intro hm a _
    rw [← lgraded_weight_rowW, hm]
  · intro hm
    funext a
    rw [lgraded_weight_rowW]
    exact hm a (Finset.mem_univ a)

end Formalism.GradedWeylDivisibility
