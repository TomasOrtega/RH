import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocTrDual

namespace Formalism.L2.SG.Pf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conductor_inverse_different : Formalism.L2.SG.Pf.NcVal.CondAll := condAll_of_locTrDual LocTr.local_trace_duality

end Formalism.L2.SG.Pf
