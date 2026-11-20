import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotIsoSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PMulQuotEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w v'

/- English proof (translation)
Introduce `k _ Ω _ _ N x E _ _ _ _ E' _ _ _ _ F₁ F₂ G₁ G₂ e`. Unfold `eulerCharQuot`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Conclude with `(Cech.equivH e.equiv e.comm i).finrank_eq`.
-/
theorem SnapperQuotIso.proof : SnapperQuotIso.Statement.{u, v, w, v'} := by
  intro k _ Ω _ _ N x E _ _ _ _ E' _ _ _ _ F₁ F₂ G₁ G₂ e
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (Cech.equivH e.equiv e.comm i).finrank_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
