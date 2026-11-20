import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.pageWord_thickOr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTwistedDualOrbitPageWordThickOr.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  first | exact @GlobalTheory.HTW.pageWord_thickOr | exact GlobalTheory.HTW.pageWord_thickOr | (intros; apply GlobalTheory.HTW.pageWord_thickOr <;> assumption)
