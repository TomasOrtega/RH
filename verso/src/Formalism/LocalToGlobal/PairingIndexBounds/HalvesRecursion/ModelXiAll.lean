import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.ModelXiNZOf
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

namespace Formalism.L2.PairingIndexBounds.Rec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modelXi_all (hH : HalvesRec) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D := modelXi_of hH D (discrNZ D)

end Formalism.L2.PairingIndexBounds.Rec
