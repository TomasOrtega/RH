import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.TwoTorsionIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeJ

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twoTorsionZ : TwoTorsionZ.{u} := two_torsion_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plusZ : PlusZ.{u} := addition_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpInU : WpInU.{u} := wpInU_of wpShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tInZ : TInZ.{u} := tInZ_of wpShape

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridgeWp : BridgeWp := bridgeWp_of wpCleared
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridgeLaw : BridgeLaw := bridgeLaw_of coeffMem fglLog halfSpec halfLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridgeCurve : BridgeCurve := bridgeCurve_of coeffMem wpInU cubeTwoR
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridgeTwo : BridgeTwo := bridgeTwo_of coeffMem tInZ twoTorsionZ

end Formalism.L2.Th1.A
