import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.WpShape
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalLogarithmBaseChange
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.SubstPairSubst

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `wpShape_of expSpec wpODE`.
-/
theorem wpShape : WpShape.{u} := wpShape_of expSpec wpODE
/- English proof (translation)
The claim follows from `wpCleared_of expSpec wpODE`.
-/
theorem wpCleared : WpCleared.{u} := wpCleared_of expSpec wpODE
/- English proof (translation)
The claim follows from `wpRecursion_of expSpec wpODE`.
-/
theorem wpRecursion : WpRecursion.{u} := wpRecursion_of expSpec wpODE

/- English proof (translation)
The claim follows from `formal_group_logarithm`.
-/
theorem fglLog : FglLog.{u} := formal_group_logarithm
/- English proof (translation)
The claim follows from `formal_group_group_law`.
-/
theorem fglGroup : FglGroup.{u} := formal_group_group_law
/- English proof (translation)
The claim follows from `formal_group_inverse`.
-/
theorem fglInv : FglInv.{u} := formal_group_inverse

/- English proof (translation)
The claim follows from `z_series_map`.
-/
theorem zSerMap : ZSerMap.{u, v} := z_series_map
/- English proof (translation)
The claim follows from `zSerLog_of fglLog`.
-/
theorem zSerLog : ZSerLog.{u} := zSerLog_of fglLog
/- English proof (translation)
The claim follows from `zSerSpec_of fglLog`.
-/
theorem zSerSpec : ZSerSpec.{u} := zSerSpec_of fglLog
/- English proof (translation)
The claim follows from `halfSpec_of fglLog`.
-/
theorem halfSpec : HalfSpec.{u} := halfSpec_of fglLog
/- English proof (translation)
The claim follows from `halfLog_of fglLog fglLog`.
-/
theorem halfLog : HalfLog.{u, v} := halfLog_of fglLog fglLog

end Formalism.L2.Th1.A
