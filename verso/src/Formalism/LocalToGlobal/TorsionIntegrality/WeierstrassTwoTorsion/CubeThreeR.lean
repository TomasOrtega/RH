import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupConstCoeffZero
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeK

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `cube_two_relation`.
-/
theorem cubeTwoR : CubeTwoR.{u} := cube_two_relation
/- English proof (translation)
The claim follows from `cube_three_relation`.
-/
theorem cubeThreeR : CubeThreeR.{u} := cube_three_relation
/- English proof (translation)
The claim follows from `coeffMem_of zSerMap halfLog`.
-/
theorem coeffMem : CoeffMem.{u} := coeffMem_of zSerMap halfLog

/- English proof (translation)
The claim follows from `short_weierstrass_inverse`.
-/
theorem shortInv : ShortInv := short_weierstrass_inverse
/- English proof (translation)
The claim follows from `wpNumEq_of wpShape wpRecursion`.
-/
theorem wpNumEq : WpNumEq := wpNumEq_of wpShape wpRecursion
/- English proof (translation)
The claim follows from `uSerEq_of wpShape wpRecursion`.
-/
theorem uSerEq : USerEq := uSerEq_of wpShape wpRecursion

end Formalism.L2.Th1.A
