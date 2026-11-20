import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SplittingOfSandwichAndPairing
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FSplittingOfSandwichAndPairing.lean&line=310#L310)
-/
theorem _root_.GlobalTheory.T.splitting_of_sandwich_and_pairing : StSandwich → StPairing → StSplit := by
  first | exact @GlobalTheory.CompanionTheory.RgSplit.stSplit | exact GlobalTheory.CompanionTheory.RgSplit.stSplit | (intros; apply GlobalTheory.CompanionTheory.RgSplit.stSplit <;> assumption)
