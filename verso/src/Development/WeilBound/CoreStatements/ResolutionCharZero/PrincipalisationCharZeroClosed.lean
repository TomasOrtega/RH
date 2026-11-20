import Mathlib
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroOfBoundary
import Development.WeilBound.CoreStatements.ResolutionCharZero.RqGbnd

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

/- English proof (translation)
The claim follows from `principalisationCharZero_of_boundary PositivityTheory.ResPlug.GBnd.gBoundary`.
-/
theorem principalisationCharZero_closed : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero :=
  principalisationCharZero_of_boundary PositivityTheory.ResPlug.GBnd.gBoundary

end PositivityTheory.ResPlug.WeightsCompactStabilizer
