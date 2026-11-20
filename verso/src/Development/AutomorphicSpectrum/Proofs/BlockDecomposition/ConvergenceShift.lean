import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

open Filter Topology

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem convShift_holds : ConvShift := by
  intro E _ _ _ N t s z z₀ h hz
  induction h with
  | leaf V w w₀ hw => exact Conv.leaf V (fun k => w k + z k) (w₀ + z₀) (hw.add hz)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
