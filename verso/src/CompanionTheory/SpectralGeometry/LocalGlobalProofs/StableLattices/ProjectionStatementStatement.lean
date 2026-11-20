import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.ProjectionStatement : StProj := by
  first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)
