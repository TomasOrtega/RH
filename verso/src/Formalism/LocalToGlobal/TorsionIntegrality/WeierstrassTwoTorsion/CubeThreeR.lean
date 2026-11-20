import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupConstCoeffZero
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeK

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cubeTwoR : CubeTwoR.{u} := cube_two_relation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cubeThreeR : CubeThreeR.{u} := cube_three_relation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coeffMem : CoeffMem.{u} := coeffMem_of zSerMap halfLog

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shortInv : ShortInv := short_weierstrass_inverse
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpNumEq : WpNumEq := wpNumEq_of wpShape wpRecursion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uSerEq : USerEq := uSerEq_of wpShape wpRecursion

end Formalism.L2.Th1.A
