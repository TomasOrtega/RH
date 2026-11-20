import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlaces
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.vacChar_of_record | exact GlobalTheory.vacChar_of_record | (intros; apply GlobalTheory.vacChar_of_record <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_atRealPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  first | exact @GlobalTheory.vacChar_of_record | exact GlobalTheory.vacChar_of_record | (intros; apply GlobalTheory.vacChar_of_record <;> assumption)
