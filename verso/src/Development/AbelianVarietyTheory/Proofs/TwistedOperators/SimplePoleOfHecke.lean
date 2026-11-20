import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont

namespace GlobalTheory.LiftPoleObj

/- English proof (translation)
The claim follows from `GlobalTheory.LiftPole.simplePole_of_hecke hH`.
-/
theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
