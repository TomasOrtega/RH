import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeparatedMovingStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgFl.stSepMove | exact GlobalTheory.CompanionTheory.RgFl.stSepMove | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSepMove <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.SeparatedMovingStatement : StSepMove := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSepMove | exact GlobalTheory.CompanionTheory.RgFl.stSepMove | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSepMove <;> assumption)
