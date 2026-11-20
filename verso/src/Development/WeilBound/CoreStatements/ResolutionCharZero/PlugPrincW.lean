import Mathlib
import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromRes

namespace PositivityTheory.ResPlug.FromRes

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem princW : PositivityTheory.ResPlug.PrincW :=
  princW_of_functorialPrincipalization FunctorialResolution.functorialPrincipalizationCharZero.{0}

end PositivityTheory.ResPlug.FromRes
