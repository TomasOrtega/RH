import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ggeo.bT_add_div_le_three_halves` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTopSizeAddLeThreeHalvesScale.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.topSize_add_le_three_halves_scale : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x → ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  first | exact @GlobalTheory.Ggeo.bT_add_div_le_three_halves | exact GlobalTheory.Ggeo.bT_add_div_le_three_halves | (intros; apply GlobalTheory.Ggeo.bT_add_div_le_three_halves <;> assumption)
