import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.vacuumFock_all_records` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFockVectorsOverVacuumIsometryOfSkeletonDatum.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.vacuumFock_all_records | exact GlobalTheory.vacuumFock_all_records | (intros; apply GlobalTheory.vacuumFock_all_records <;> assumption)
