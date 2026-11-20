import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SplittingOfSandwichAndPairing
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgSplit.stSplit | exact GlobalTheory.CompanionTheory.RgSplit.stSplit | (intros; apply GlobalTheory.CompanionTheory.RgSplit.stSplit <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.splitting_of_sandwich_and_pairing : StSandwich → StPairing → StSplit := by
  first | exact @GlobalTheory.CompanionTheory.RgSplit.stSplit | exact GlobalTheory.CompanionTheory.RgSplit.stSplit | (intros; apply GlobalTheory.CompanionTheory.RgSplit.stSplit <;> assumption)
