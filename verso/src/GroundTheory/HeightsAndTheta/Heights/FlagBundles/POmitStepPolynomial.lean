import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem OmitStepPolynomial.proof : OmitStepPolynomial.Statement := by
  intro R _ σ _ p
  refine ⟨((renameEquiv R (Equiv.optionSubtypeNe p).symm).trans
      (optionEquivLeft R {q // q ≠ p})).toRingEquiv, ?_, ?_, ?_⟩
  · simp [optionEquivLeft_X_none]
  · intro q
    simp [Equiv.optionSubtypeNe_symm_of_ne q.property, optionEquivLeft_X_some]
  · intro r
    simp [optionEquivLeft_C]

end GroundTheory.Heights₂.Heights.FlagBundles
