import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FStTensor.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.stTensor' : StTensor := by
  first | exact @GlobalTheory.CompanionTheory.RestT.stTensor | exact GlobalTheory.CompanionTheory.RestT.stTensor | (intros; apply GlobalTheory.CompanionTheory.RestT.stTensor <;> assumption)
