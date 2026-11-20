import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IntegerEndomorphismInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp

namespace Formalism.L2.Th1.F

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorRing : TaylorRing := taylor_ring
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorDeriv : TaylorDeriv := taylor_deriv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorExp : TaylorExp := taylor_exp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorSigma : TaylorSigma := taylorSigma_of taylorRing taylorDeriv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorSgStar : TaylorSgStar := taylorSgStar_of taylorSigma taylorRing taylorExp sigmaEntire
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pSeriesCoeff : PSeriesCoeff := weierstrass_p_series_coeff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem taylorIsWp : TaylorIsWp := taylorIsWp_of taylorRing taylorDeriv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isWpUnique : IsWpUnique := weierstrass_series_unique
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endoZInstance : EndoZInstance := integer_endomorphism_instance
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isogenyFormulaInstance : IsogenyFormulaInstance := isogeny_formula_instance

end Formalism.L2.Th1.F
