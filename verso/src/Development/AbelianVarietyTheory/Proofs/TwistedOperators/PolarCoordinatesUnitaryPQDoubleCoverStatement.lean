import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCover
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.PolarU.polar_coordinates | exact GlobalTheory.PolarU.polar_coordinates | (intros; apply GlobalTheory.PolarU.polar_coordinates <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover : ∀ X : ProvA, CoverHaarIntegration X := by
  first | exact @GlobalTheory.PolarU.polar_coordinates | exact GlobalTheory.PolarU.polar_coordinates | (intros; apply GlobalTheory.PolarU.polar_coordinates <;> assumption)
