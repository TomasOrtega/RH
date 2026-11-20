import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MkLeOfDenseRange
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Universal

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `weierstrass_numerator_denominator`.
-/
theorem wpNumDen : WpNumDen := weierstrass_numerator_denominator
/- English proof (translation)
The claim follows from `weierstrass_p_of_series`.
-/
theorem pOfIsWp : POfIsWp := weierstrass_p_of_series
/- English proof (translation)
The claim follows from `weierstrass_p_of_lattice`.
-/
theorem pOfLattice : POfLattice := weierstrass_p_of_lattice
/- English proof (translation)
The claim follows from `curve_weierstrass_series_eq`.
-/
theorem curveBridge : CurveBridge := curve_weierstrass_series_eq
/- English proof (translation)
The claim follows from `iotaExists_thm`.
-/
theorem iotaExists : IotaExists := iotaExists_thm
/- English proof (translation)
The claim follows from `sigma_universal`.
-/
theorem sigmaUniversal : SigmaUniversal := sigma_universal
/- English proof (translation)
The claim follows from `hasCMByIsogeny_of' isogenyFormulaInstance`.
-/
theorem hasCMByIsogeny : HasCMByIsogeny := hasCMByIsogeny_of' isogenyFormulaInstance

end Formalism.L2.Th1.F
