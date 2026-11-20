import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrabilityStatement

open Formalism.BasicNotions

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.T.fockVectors_overVacuum_isometry`.
-/
theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := GlobalTheory.T.fockVectors_overVacuum_isometry

end GlobalTheory
