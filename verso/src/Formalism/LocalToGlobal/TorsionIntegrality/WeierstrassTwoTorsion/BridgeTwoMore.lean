import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DifferenceLinearCoeff
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.NormLeOneOfMonicTwo
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.WeierstrassPPrimeUnit

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridgeTwoMore : BridgeTwoMore := two_curves_relation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowUniqueZ : FlowUniqueZ.{u} := flow_unique_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridgeCurve3 : BridgeCurve3 := three_curves_relation

end Formalism.L2.Th1.A
