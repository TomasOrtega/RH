import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

namespace GlobalTheory

/- English proof (translation)
The claim follows from `CompanionTheory.D.DSIC.discrete_series_infinitesimal_character`.
-/
theorem capelliDiscreteSeriesInfChar : PI.DSInfCharCap.DSInfCharCap :=
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end GlobalTheory
