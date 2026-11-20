import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsUFD
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

/- English proof (translation)
Introduce `d y`. Use `hU (Fin d) y` as an intermediate fact. Conclude with `⟨HolGermsDomain.proof (Fin d) y, inferInstance⟩`.
-/
theorem HolGermsIntegrallyClosed.proof (hU : HolGermsUFD.Statement) : HolGermsIntegrallyClosed.Statement := by
  intro d y
  have := hU (Fin d) y
  exact ⟨HolGermsDomain.proof (Fin d) y, inferInstance⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
