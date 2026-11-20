import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenyP
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassPSecondDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.CmAlternatingForm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenySigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly

namespace Formalism.L2.Th1.F

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latticeOnly : LatticeOnly := lattice_only
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem homogeneity : Homogeneity := homogeneity_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kerRepsExist : KerRepsExist := kernel_reps_exist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kerRepsCard : KerRepsCard := kernel_reps_card
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulStableIntegral : MulStableIntegral := mul_stable_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isogenyP : IsogenyP := isogenyWeierstrassP_of_ellipticNoPole ellipticNoPole
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pSecond : PSecond := weierstrass_p_second_derivative
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isogenySigma : IsogenySigma :=
  isogenySigma_of ellipticNoPole sigmaOrder sgStarAdd sgStarQuasi sgStarBasic kerRepsCard sigmaEntire
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem translateProduct : TranslateProduct := translateProduct_of sgStarAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem halfShift : HalfShift := halfShift_of sigmaAdd sigmaQuasi sigmaZero pInjective
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmThetaEq : CmThetaEq := cm_theta_eq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmStable : CmStable := cm_stable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmOrder : CmOrder := cm_order
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmArea : CmArea := cm_area
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmNorm : CmNorm := cm_norm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmAltE : CmAltE := cm_alternating_form
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmHalfLatticeIff : CMHalfLatticeIff := cm_half_lattice_iff

end Formalism.L2.Th1.F
