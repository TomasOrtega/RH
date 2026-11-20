import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FPairingStatement.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.PairingStatement : StPair := by
  first | exact @GlobalTheory.CompanionTheory.HeckePair.stPair | exact GlobalTheory.CompanionTheory.HeckePair.stPair | (intros; apply GlobalTheory.CompanionTheory.HeckePair.stPair <;> assumption)
