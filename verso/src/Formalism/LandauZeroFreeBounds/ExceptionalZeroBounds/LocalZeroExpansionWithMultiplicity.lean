import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Introduce `f z₀ r M hr hM hf hfz₀ hbound`. Take `⟨Z, m, h1, h2, h3, -, h5, h6⟩` from `exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound`. Conclude with `⟨Z, m, h1, h2, h3, h5, h6⟩`.
-/
theorem localZeroExpansionWithMultiplicity : LandauLocal2 := by
  intro f z₀ r M hr hM hf hfz₀ hbound
  obtain ⟨Z, m, h1, h2, h3, -, h5, h6⟩ := exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound
  exact ⟨Z, m, h1, h2, h3, h5, h6⟩

end Formalism.ZeroFreeDirichlet
