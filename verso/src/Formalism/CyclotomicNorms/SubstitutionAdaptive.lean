import Formalism.CyclotomicNorms.NonsquarefreeBounds.AdaptiveSubstitutionBound
import Formalism.CyclotomicNorms.NonsquarefreeBounds.LowDegreePowerSeries
import Formalism.CyclotomicNorms.NonsquarefreeBounds.TwoMulNumDerangementsLeFactorial
import Formalism.CyclotomicNorms.StatementI

namespace Formalism.CyclotomicNorms

/- English proof (translation)
The claim follows from `adaptive_substitution_bound`.
-/
theorem substitutionAdaptive : SubstitutionAdaptive := adaptive_substitution_bound
/- English proof (translation)
The claim follows from `low_degree_power_series`.
-/
theorem lowPowerSeries : LowPowerSeries := low_degree_power_series

end Formalism.CyclotomicNorms
