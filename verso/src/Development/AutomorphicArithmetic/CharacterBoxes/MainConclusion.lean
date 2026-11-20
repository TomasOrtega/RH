import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter

/- English proof (authored)
The row hypothesis supplies the two row entries of the literature interface. Fill its local reciprocity existence entry with `recTExists`. The same row hypothesis gives the window estimate by `vwin_of_row`. Apply `every_character_of_literature_of_vWin` to the interface and the window estimate.
-/
theorem UpperTheory.FinalTheorems.everyCharacter_of_row (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) : UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin ⟨h, UpperTheory.Zero.LLC.recTExists, h⟩ (UpperTheory.One.vwin_of_row h)

/- English proof (authored)
The integral Galois compatibility theorem `galoisLocalGlobalStrong_recParameter` provides the row for the local reciprocity parameter. Use that row in `everyCharacter_of_row` to obtain nonvanishing for every character.
-/
theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter

/- English proof (authored)
Apply `riemannHypothesis_of_everyCharacter` with the nonvanishing result `UpperTheory.FinalTheorems.everyCharacter`.
-/
theorem UpperTheory.FinalTheorems.riemannHypothesis : RiemannHypothesis :=
  UpperTheory.riemannHypothesis_of_everyCharacter UpperTheory.FinalTheorems.everyCharacter
