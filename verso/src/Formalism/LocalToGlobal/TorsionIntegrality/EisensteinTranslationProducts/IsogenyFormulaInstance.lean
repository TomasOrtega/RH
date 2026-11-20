import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IntegerEndomorphismInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `taylor_ring`.
-/
theorem taylorRing : TaylorRing := taylor_ring
/- English proof (translation)
The claim follows from `taylor_deriv`.
-/
theorem taylorDeriv : TaylorDeriv := taylor_deriv
/- English proof (translation)
The claim follows from `taylor_exp`.
-/
theorem taylorExp : TaylorExp := taylor_exp
/- English proof (translation)
The claim follows from `taylorSigma_of taylorRing taylorDeriv`.
-/
theorem taylorSigma : TaylorSigma := taylorSigma_of taylorRing taylorDeriv
/- English proof (translation)
The claim follows from `taylorSgStar_of taylorSigma taylorRing taylorExp sigmaEntire`.
-/
theorem taylorSgStar : TaylorSgStar := taylorSgStar_of taylorSigma taylorRing taylorExp sigmaEntire
/- English proof (translation)
The claim follows from `weierstrass_p_series_coeff`.
-/
theorem pSeriesCoeff : PSeriesCoeff := weierstrass_p_series_coeff
/- English proof (translation)
The claim follows from `taylorIsWp_of taylorRing taylorDeriv`.
-/
theorem taylorIsWp : TaylorIsWp := taylorIsWp_of taylorRing taylorDeriv
/- English proof (translation)
The claim follows from `weierstrass_series_unique`.
-/
theorem isWpUnique : IsWpUnique := weierstrass_series_unique
/- English proof (translation)
The claim follows from `integer_endomorphism_instance`.
-/
theorem endoZInstance : EndoZInstance := integer_endomorphism_instance
/- English proof (translation)
The claim follows from `isogeny_formula_instance`.
-/
theorem isogenyFormulaInstance : IsogenyFormulaInstance := isogeny_formula_instance

end Formalism.L2.Th1.F
