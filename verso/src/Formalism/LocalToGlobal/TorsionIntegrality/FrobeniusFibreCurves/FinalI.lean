import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalE
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PhENormOf
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoAdicScalarConditions
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionCurveToSeries

namespace Formalism.L2.Th1.B

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Isogeny : Th0Isogeny := Iso.theta_zero_isogeny_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phENorm : PhENorm := Nrm.PhENorm_of th0Isogeny
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Vanish : ThetaZeroVanishing := Van.Th0Vanish_of cubeE phENorm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twoAdicScalars : TwoAdicScalars := Van.two_adic_scalar_conditions

end Formalism.L2.Th1.B
