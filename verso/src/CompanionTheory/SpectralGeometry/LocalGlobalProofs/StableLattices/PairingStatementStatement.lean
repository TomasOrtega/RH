import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.HeckePair.stPair | exact GlobalTheory.CompanionTheory.HeckePair.stPair | (intros; apply GlobalTheory.CompanionTheory.HeckePair.stPair <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.PairingStatement : StPair := by
  first | exact @GlobalTheory.CompanionTheory.HeckePair.stPair | exact GlobalTheory.CompanionTheory.HeckePair.stPair | (intros; apply GlobalTheory.CompanionTheory.HeckePair.stPair <;> assumption)
