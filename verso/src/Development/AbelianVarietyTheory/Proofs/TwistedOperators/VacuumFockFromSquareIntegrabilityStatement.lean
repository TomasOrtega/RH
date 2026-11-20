import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FVacuumFockFromSquareIntegrability.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.fockVectors_overVacuum_isometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.VacuumFockLaws.vacuumFock_onObjects | exact GlobalTheory.VacuumFockLaws.vacuumFock_onObjects | (intros; apply GlobalTheory.VacuumFockLaws.vacuumFock_onObjects <;> assumption)
