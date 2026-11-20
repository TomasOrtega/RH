import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalE
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PhENormOf
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoAdicScalarConditions
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionCurveToSeries

namespace Formalism.L2.Th1.B

/- English proof (translation)
The claim follows from `Iso.theta_zero_isogeny_holds`.
-/
theorem th0Isogeny : Th0Isogeny := Iso.theta_zero_isogeny_holds
/- English proof (translation)
The claim follows from `Nrm.PhENorm_of th0Isogeny`.
-/
theorem phENorm : PhENorm := Nrm.PhENorm_of th0Isogeny
/- English proof (translation)
The claim follows from `Van.Th0Vanish_of cubeE phENorm`.
-/
theorem th0Vanish : ThetaZeroVanishing := Van.Th0Vanish_of cubeE phENorm
/- English proof (translation)
The claim follows from `Van.two_adic_scalar_conditions`.
-/
theorem twoAdicScalars : TwoAdicScalars := Van.two_adic_scalar_conditions

end Formalism.L2.Th1.B
