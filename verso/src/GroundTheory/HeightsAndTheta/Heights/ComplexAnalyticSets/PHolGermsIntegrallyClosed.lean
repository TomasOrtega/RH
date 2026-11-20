import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsUFD
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem HolGermsIntegrallyClosed.proof (hU : HolGermsUFD.Statement) : HolGermsIntegrallyClosed.Statement := by
  intro d y
  have := hU (Fin d) y
  exact ⟨HolGermsDomain.proof (Fin d) y, inferInstance⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
