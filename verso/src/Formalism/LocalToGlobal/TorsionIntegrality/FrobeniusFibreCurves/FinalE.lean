import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffQuotientXSq
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.AtVariableWeierstrassDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.DivLaw
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CocycleDiffExpEquiv

namespace Formalism.L2.Th1.B

/- English proof (translation)
The claim follows from `SAdd.weierstrass_addition_holds`.
-/
theorem wAdd : WAdd := SAdd.weierstrass_addition_holds
/- English proof (translation)
The claim follows from `GCob.weierstrass_derivative_unit_holds`.
-/
theorem wPrimeU : WPrimeU := GCob.weierstrass_derivative_unit_holds
/- English proof (translation)
The claim follows from `GCob.GCob_of wAdd wPrimeU`.
-/
theorem gCob : GCob := GCob.GCob_of wAdd wPrimeU
/- English proof (translation)
The claim follows from `LDiv.LDiv_of gCob`.
-/
theorem lDiv : LDiv := LDiv.LDiv_of gCob
/- English proof (translation)
The claim follows from `BeE.BeESim_of gCob lDiv`.
-/
theorem beESim : BeESim := BeE.BeESim_of gCob lDiv
/- English proof (translation)
The claim follows from `BeE.cocycle_diff_exp_equiv`.
-/
theorem first_cocycle_simeq_zero : CocycleDiffExpEquiv := BeE.cocycle_diff_exp_equiv
/- English proof (translation)
The claim follows from `BeE.CubeE_of beESim first_cocycle_simeq_zero`.
-/
theorem cubeE : CubeE := BeE.CubeE_of beESim first_cocycle_simeq_zero

end Formalism.L2.Th1.B
