import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HasCMByIsogenyOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaScale

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `has_cm_stable`.
-/
theorem hasCMByStable : HasCMByStable := has_cm_stable
/- English proof (translation)
The claim follows from `has_cm_scale`.
-/
theorem hasCMByScale : HasCMByScale := has_cm_scale
/- English proof (translation)
The claim follows from `cm_pair_has_cm`.
-/
theorem cmPairHasCMBy : CmPairHasCMBy := cm_pair_has_cm
/- English proof (translation)
The claim follows from `j_invariant_scale`.
-/
theorem jInvScale : JInvScale := j_invariant_scale
/- English proof (translation)
The claim follows from `series_scale`.
-/
theorem seriesScale : SeriesScale := series_scale
/- English proof (translation)
The claim follows from `sigma_scale'`.
-/
theorem sigmaScale : SigmaScale := sigma_scale'
/- English proof (translation)
The claim follows from `series_map`.
-/
theorem seriesMap : SeriesMap := series_map

end Formalism.L2.Th1.F
