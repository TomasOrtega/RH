import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DivisionLogarithm

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `division_spec`.
-/
theorem divSpec : DivSpec.{u, v} := division_spec

end Formalism.L2.Th1.A
