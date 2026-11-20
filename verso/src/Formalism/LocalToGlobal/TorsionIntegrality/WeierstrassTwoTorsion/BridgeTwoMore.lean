import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DifferenceLinearCoeff
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.NormLeOneOfMonicTwo
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.WeierstrassPPrimeUnit

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `two_curves_relation`.
-/
theorem bridgeTwoMore : BridgeTwoMore := two_curves_relation
/- English proof (translation)
The claim follows from `flow_unique_integral`.
-/
theorem flowUniqueZ : FlowUniqueZ.{u} := flow_unique_integral
/- English proof (translation)
The claim follows from `three_curves_relation`.
-/
theorem bridgeCurve3 : BridgeCurve3 := three_curves_relation

end Formalism.L2.Th1.A
