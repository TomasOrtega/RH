import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanish
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TypeConstTerm.typeConstTermVanish | exact GlobalTheory.TypeConstTerm.typeConstTermVanish | (intros; apply GlobalTheory.TypeConstTerm.typeConstTermVanish <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.typeIdempotent_constantTerm_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish := by
  first | exact @GlobalTheory.TypeConstTerm.typeConstTermVanish | exact GlobalTheory.TypeConstTerm.typeConstTermVanish | (intros; apply GlobalTheory.TypeConstTerm.typeConstTermVanish <;> assumption)
