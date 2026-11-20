import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
Apply the local zero expansion theorem to the given function, disk, and relative growth bound. Its full conclusion gives the zero list, multiplicities, total count, and logarithmic derivative error required here.
-/
theorem landau_local3 : LandauLocal3 :=
  fun f z₀ r M hr hM hf hfz₀ hbound => exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound

end Formalism.ZeroFreeDirichlet
