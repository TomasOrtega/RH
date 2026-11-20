import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
import Development.WeilBound.CoreStatements.ResolutionCharZero.ResolutionCharZeroOfTop

namespace PositivityTheory.Resplug.ResolutionBlowup

/- English proof (translation)
The claim follows from `resolutionCharZero_of_top FunctorialResolution.functorialResolutionCharZero.{0}`.
-/
theorem resolutionCharZero : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero :=
  resolutionCharZero_of_top FunctorialResolution.functorialResolutionCharZero.{0}

end PositivityTheory.Resplug.ResolutionBlowup
