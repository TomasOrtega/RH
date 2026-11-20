import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLin

namespace Formalism.IndefR.Fin

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem splitLinF (D : Formalism.BasicNotions.D7) : SplitLin D := splitLin_of (placeLatDual D) (latLevelF D)

end Formalism.IndefR.Fin
