import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.TwoTorsionIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeJ

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `two_torsion_integral`.
-/
theorem twoTorsionZ : TwoTorsionZ.{u} := two_torsion_integral
/- English proof (translation)
The claim follows from `addition_integral`.
-/
theorem plusZ : PlusZ.{u} := addition_integral
/- English proof (translation)
The claim follows from `wpInU_of wpShape`.
-/
theorem wpInU : WpInU.{u} := wpInU_of wpShape
/- English proof (translation)
The claim follows from `tInZ_of wpShape`.
-/
theorem tInZ : TInZ.{u} := tInZ_of wpShape

/- English proof (translation)
The claim follows from `bridgeWp_of wpCleared`.
-/
theorem bridgeWp : BridgeWp := bridgeWp_of wpCleared
/- English proof (translation)
The claim follows from `bridgeLaw_of coeffMem fglLog halfSpec halfLog`.
-/
theorem bridgeLaw : BridgeLaw := bridgeLaw_of coeffMem fglLog halfSpec halfLog
/- English proof (translation)
The claim follows from `bridgeCurve_of coeffMem wpInU cubeTwoR`.
-/
theorem bridgeCurve : BridgeCurve := bridgeCurve_of coeffMem wpInU cubeTwoR
/- English proof (translation)
The claim follows from `bridgeTwo_of coeffMem tInZ twoTorsionZ`.
-/
theorem bridgeTwo : BridgeTwo := bridgeTwo_of coeffMem tInZ twoTorsionZ

end Formalism.L2.Th1.A
