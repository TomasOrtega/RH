import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeRoundedSizeBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMulSmallBoundsLeRoundedSizeBound.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.mul_smallBounds_le_roundedSizeBound : ∀ {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ), Roomy L C' → 0 ≤ C → 2 * C ≤ C' → 2 * j + 2 ≤ D.host.Lw → C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  first | exact @GlobalTheory.HTW.mul_small_le_bHat | exact GlobalTheory.HTW.mul_small_le_bHat | (intros; apply GlobalTheory.HTW.mul_small_le_bHat <;> assumption)
