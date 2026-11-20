import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FrameTorus.stTor | exact GlobalTheory.CompanionTheory.FrameTorus.stTor | (intros; apply GlobalTheory.CompanionTheory.FrameTorus.stTor <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.TorusStatement : StTor := by
  first | exact @GlobalTheory.CompanionTheory.FrameTorus.stTor | exact GlobalTheory.CompanionTheory.FrameTorus.stTor | (intros; apply GlobalTheory.CompanionTheory.FrameTorus.stTor <;> assumption)
