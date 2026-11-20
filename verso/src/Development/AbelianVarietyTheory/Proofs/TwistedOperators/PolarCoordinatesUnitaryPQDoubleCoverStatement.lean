import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCover
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolarU.polar_coordinates` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPolarCoordinatesUnitaryPQDoubleCover.lean&line=153#L153)
-/
theorem _root_.GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover : ∀ X : ProvA, CoverHaarIntegration X := by
  first | exact @GlobalTheory.PolarU.polar_coordinates | exact GlobalTheory.PolarU.polar_coordinates | (intros; apply GlobalTheory.PolarU.polar_coordinates <;> assumption)
