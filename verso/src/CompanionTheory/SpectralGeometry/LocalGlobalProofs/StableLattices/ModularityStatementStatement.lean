import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ModularityStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.HeckeCoinv.stMod | exact GlobalTheory.CompanionTheory.HeckeCoinv.stMod | (intros; apply GlobalTheory.CompanionTheory.HeckeCoinv.stMod <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.ModularityStatement : StMod := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCoinv.stMod | exact GlobalTheory.CompanionTheory.HeckeCoinv.stMod | (intros; apply GlobalTheory.CompanionTheory.HeckeCoinv.stMod <;> assumption)
