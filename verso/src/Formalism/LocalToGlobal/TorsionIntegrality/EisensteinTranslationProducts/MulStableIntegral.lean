import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenyP
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassPSecondDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.CmAlternatingForm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IsogenySigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `lattice_only`.
-/
theorem latticeOnly : LatticeOnly := lattice_only
/- English proof (translation)
The claim follows from `homogeneity_thm`.
-/
theorem homogeneity : Homogeneity := homogeneity_thm
/- English proof (translation)
The claim follows from `kernel_reps_exist`.
-/
theorem kerRepsExist : KerRepsExist := kernel_reps_exist
/- English proof (translation)
The claim follows from `kernel_reps_card`.
-/
theorem kerRepsCard : KerRepsCard := kernel_reps_card
/- English proof (translation)
The claim follows from `mul_stable_integral`.
-/
theorem mulStableIntegral : MulStableIntegral := mul_stable_integral
/- English proof (translation)
The claim follows from `isogenyWeierstrassP_of_ellipticNoPole ellipticNoPole`.
-/
theorem isogenyP : IsogenyP := isogenyWeierstrassP_of_ellipticNoPole ellipticNoPole
/- English proof (translation)
The claim follows from `weierstrass_p_second_derivative`.
-/
theorem pSecond : PSecond := weierstrass_p_second_derivative
/- English proof (translation)
The claim follows from `isogenySigma_of ellipticNoPole sigmaOrder sgStarAdd sgStarQuasi sgStarBasic kerRepsCard sigmaEntire`.
-/
theorem isogenySigma : IsogenySigma :=
  isogenySigma_of ellipticNoPole sigmaOrder sgStarAdd sgStarQuasi sgStarBasic kerRepsCard sigmaEntire
/- English proof (translation)
The claim follows from `translateProduct_of sgStarAdd`.
-/
theorem translateProduct : TranslateProduct := translateProduct_of sgStarAdd
/- English proof (translation)
The claim follows from `halfShift_of sigmaAdd sigmaQuasi sigmaZero pInjective`.
-/
theorem halfShift : HalfShift := halfShift_of sigmaAdd sigmaQuasi sigmaZero pInjective
/- English proof (translation)
The claim follows from `cm_theta_eq`.
-/
theorem cmThetaEq : CmThetaEq := cm_theta_eq
/- English proof (translation)
The claim follows from `cm_stable`.
-/
theorem cmStable : CmStable := cm_stable
/- English proof (translation)
The claim follows from `cm_order`.
-/
theorem cmOrder : CmOrder := cm_order
/- English proof (translation)
The claim follows from `cm_area`.
-/
theorem cmArea : CmArea := cm_area
/- English proof (translation)
The claim follows from `cm_norm`.
-/
theorem cmNorm : CmNorm := cm_norm
/- English proof (translation)
The claim follows from `cm_alternating_form`.
-/
theorem cmAltE : CmAltE := cm_alternating_form
/- English proof (translation)
The claim follows from `cm_half_lattice_iff`.
-/
theorem cmHalfLatticeIff : CMHalfLatticeIff := cm_half_lattice_iff

end Formalism.L2.Th1.F
