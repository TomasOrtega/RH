import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

namespace LateralTheory.CohomologicalPurity

/- English proof (translation)
Introduce `H` and use `⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩`.
-/
theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
