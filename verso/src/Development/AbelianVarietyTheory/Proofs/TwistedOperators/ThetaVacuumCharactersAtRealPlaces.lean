import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement

open Formalism.BasicNotions

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.T.thetaVacuumCharacters_realPlaces`.
-/
theorem vacChar_of_record : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D :=
  GlobalTheory.T.thetaVacuumCharacters_realPlaces

end GlobalTheory
