import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.WpShape
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalLogarithmBaseChange
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.SubstPairSubst

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpShape : WpShape.{u} := wpShape_of expSpec wpODE
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpCleared : WpCleared.{u} := wpCleared_of expSpec wpODE
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpRecursion : WpRecursion.{u} := wpRecursion_of expSpec wpODE

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fglLog : FglLog.{u} := formal_group_logarithm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fglGroup : FglGroup.{u} := formal_group_group_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fglInv : FglInv.{u} := formal_group_inverse

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zSerMap : ZSerMap.{u, v} := z_series_map
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zSerLog : ZSerLog.{u} := zSerLog_of fglLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zSerSpec : ZSerSpec.{u} := zSerSpec_of fglLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem halfSpec : HalfSpec.{u} := halfSpec_of fglLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem halfLog : HalfLog.{u, v} := halfLog_of fglLog fglLog

end Formalism.L2.Th1.A
