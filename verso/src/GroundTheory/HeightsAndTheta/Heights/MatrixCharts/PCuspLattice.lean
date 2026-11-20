import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

/- English proof (translation)
Introduce `D T`. Take `⟨c₁, hc₁, H1⟩` from `h1 D T`. Take `⟨c₂, hc₂, H3⟩` from `h3 D T`. Conclude with `⟨c₁, c₂, hc₁, hc₂, fun p hp hu ℓ hℓ => ⟨H1 p hp hu ℓ hℓ, h2 D T p hp hu ℓ hℓ, fun k v hv hli => H3 p hp hu ℓ hℓ k v hv hli⟩⟩`.
-/
theorem CuspLattice.proof (h1 : CuspShortVectors.Statement) (h2 : CuspLeadingMinima.Statement)
    (h3 : CuspCovolume.Statement) : CuspLattice.Statement := by
  intro D T
  obtain ⟨c₁, hc₁, H1⟩ := h1 D T
  obtain ⟨c₂, hc₂, H3⟩ := h3 D T
  exact ⟨c₁, c₂, hc₁, hc₂, fun p hp hu ℓ hℓ =>
    ⟨H1 p hp hu ℓ hℓ, h2 D T p hp hu ℓ hℓ, fun k v hv hli => H3 p hp hu ℓ hℓ k v hv hli⟩⟩

end

end GroundTheory.Heights₂.Heights
