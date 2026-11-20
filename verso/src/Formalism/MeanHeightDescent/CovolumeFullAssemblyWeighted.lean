import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements

namespace Formalism.ExtensionFiltration

/- English proof (translation)
The claim follows from `period_bound'`.
-/
theorem periodBound : PeriodBound := period_bound'
/- English proof (translation)
The claim follows from `covolume_assembly_weighted_holds`.
-/
theorem covolume_assembly_weighted : CovolumeEstimateAnchoredWeights := covolume_assembly_weighted_holds
/- English proof (translation)
The claim follows from `covolume_full_assembly_weighted_holds`.
-/
theorem covolume_full_assembly_weighted : CovolumeEstimateOfAverageDegreeWeighted := covolume_full_assembly_weighted_holds

end Formalism.ExtensionFiltration
