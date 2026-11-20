import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MkLeOfDenseRange
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Universal

namespace Formalism.L2.Th1.F

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpNumDen : WpNumDen := weierstrass_numerator_denominator
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pOfIsWp : POfIsWp := weierstrass_p_of_series
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pOfLattice : POfLattice := weierstrass_p_of_lattice
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem curveBridge : CurveBridge := curve_weierstrass_series_eq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iotaExists : IotaExists := iotaExists_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaUniversal : SigmaUniversal := sigma_universal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hasCMByIsogeny : HasCMByIsogeny := hasCMByIsogeny_of' isogenyFormulaInstance

end Formalism.L2.Th1.F
