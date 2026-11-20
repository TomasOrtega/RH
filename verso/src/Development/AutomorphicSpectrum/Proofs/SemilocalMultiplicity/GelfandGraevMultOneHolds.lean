import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
open Formalism.L2.SG.GGMirabolic

namespace GlobalTheory.CompanionTheory.GG

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Closed.GelfandGraevMultOne_holds`.
-/
theorem gelfandGraevMultOne_holds : GelfandGraevMultOne :=
  Formalism.L2.SG.Closed.GelfandGraevMultOne_holds

end GlobalTheory.CompanionTheory.GG
