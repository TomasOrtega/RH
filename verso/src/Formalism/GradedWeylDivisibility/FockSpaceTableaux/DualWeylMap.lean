import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem dualWeylModuleMap : DualWeylMap := by
  intro R S _ _ φ r n ν f hf
  rw [lsat_mem_dualWeyl] at hf ⊢
  refine ⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩
  rw [← lsat_map_colAddGen, hf.2 l j hlj, map_rename]

end Formalism.GradedWeylDivisibility
