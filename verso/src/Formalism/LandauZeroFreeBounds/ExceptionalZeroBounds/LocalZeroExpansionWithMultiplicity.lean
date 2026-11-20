import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
The local zero expansion supplies the finite zero list and positive multiplicities, the lower bound at a vanishing derivative, the total multiplicity bound, and the derivative estimate. Retain these conclusions to obtain the asserted form.
-/
theorem localZeroExpansionWithMultiplicity : LandauLocal2 := by
  intro f z₀ r M hr hM hf hfz₀ hbound
  obtain ⟨Z, m, h1, h2, h3, -, h5, h6⟩ := exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound
  exact ⟨Z, m, h1, h2, h3, h5, h6⟩

end Formalism.ZeroFreeDirichlet
