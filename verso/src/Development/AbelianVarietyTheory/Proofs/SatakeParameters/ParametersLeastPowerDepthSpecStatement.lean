import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeastPowerDepthSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.depth_spec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLeastPowerDepthSpec.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.leastPowerDepth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l → LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧ ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  first | exact @GlobalTheory.depth_spec | exact GlobalTheory.depth_spec | (intros; apply GlobalTheory.depth_spec <;> assumption)
