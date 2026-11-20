import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceAt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem placeModelAtF (D : Formalism.BasicNotions.D7) : PlaceModelAt D := placeModelAt_of (placeLatDual D)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latLevelF (D : Formalism.BasicNotions.D7) : LatLevel D := latLevel_of (latSelfDual D)

end Formalism.IndefR.Fin

end
