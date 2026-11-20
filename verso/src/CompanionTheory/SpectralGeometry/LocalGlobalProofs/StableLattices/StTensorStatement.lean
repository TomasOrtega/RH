import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RestT.stTensor | exact GlobalTheory.CompanionTheory.RestT.stTensor | (intros; apply GlobalTheory.CompanionTheory.RestT.stTensor <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.stTensor' : StTensor := by
  first | exact @GlobalTheory.CompanionTheory.RestT.stTensor | exact GlobalTheory.CompanionTheory.RestT.stTensor | (intros; apply GlobalTheory.CompanionTheory.RestT.stTensor <;> assumption)
