import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLin

namespace Formalism.IndefR.Fin

/- English proof (translation)
The claim follows from `splitLin_of (placeLatDual D) (latLevelF D)`.
-/
theorem splitLinF (D : Formalism.BasicNotions.D7) : SplitLin D := splitLin_of (placeLatDual D) (latLevelF D)

end Formalism.IndefR.Fin
