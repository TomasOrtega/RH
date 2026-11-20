import Formalism.HermitianCurvature.StatementB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.DS.Xi.xiExists`.
-/
theorem exists_auxiliary_xi : Formalism.FourierDecayAlt.B.XiExists := ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end Formalism.FourierDecayAlt.P
