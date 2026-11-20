import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NonVac
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds

namespace Formalism.L2.Th1.D

/- English proof (translation)
The claim follows from `chain_nonvacuous`.
-/
theorem chainNonVacuous : ChainNonVacuous := chain_nonvacuous
/- English proof (translation)
The claim follows from `second_level_of_norm_holds`.
-/
theorem second_level_of_norm : SecondLevelOfNorm := second_level_of_norm_holds
/- English proof (translation)
The claim follows from `split_phi`.
-/
theorem splitPh : SplitPh := split_phi
/- English proof (translation)
The claim follows from `norm_units_alt`.
-/
theorem normUnits : NormUnits := norm_units_alt
/- English proof (translation)
The claim follows from `fixed_linear`.
-/
theorem fixedLinear : FixedLinear := fixed_linear

end Formalism.L2.Th1.D
