import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FTransferStatementBis.lean&line=171#L171)
-/
theorem _root_.GlobalTheory.T.TransferStatementBis : StTransfer := by
  first | exact @GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | exact GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | (intros; apply GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer <;> assumption)
