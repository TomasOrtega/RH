import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FPairingOfSandwichStatement.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.pairing_of_sandwich_statement : StSandwich → StPairing := by
  first | exact @GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | exact GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | (intros; apply GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich <;> assumption)
