import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocTrDual

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `condAll_of_locTrDual LocTr.local_trace_duality`.
-/
theorem conductor_inverse_different : Formalism.L2.SG.Pf.NcVal.CondAll := condAll_of_locTrDual LocTr.local_trace_duality

end Formalism.L2.SG.Pf
