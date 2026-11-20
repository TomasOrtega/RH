import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

namespace LateralTheory.CohomologicalPurity

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
