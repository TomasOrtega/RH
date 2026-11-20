import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Introduce `f z₀ r M hr hM hf hfz₀ hbound` and use `exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound`.
-/
theorem landau_local3 : LandauLocal3 :=
  fun f z₀ r M hr hM hf hfz₀ hbound => exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound

end Formalism.ZeroFreeDirichlet
