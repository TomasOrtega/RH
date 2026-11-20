import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbit
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.LongWindow.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAtMostTwoThickInWindowLongOrbit.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.atMostTwoThick_in_window_long_orbit : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 → WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  first | exact @GlobalTheory.HTW.LongWindow.main | exact GlobalTheory.HTW.LongWindow.main | (intros; apply GlobalTheory.HTW.LongWindow.main <;> assumption)
