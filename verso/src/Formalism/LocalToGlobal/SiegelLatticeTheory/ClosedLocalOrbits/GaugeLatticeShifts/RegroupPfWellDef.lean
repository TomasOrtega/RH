import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

/- English proof (translation)
Introduce `_ X _ u _` and use `Formalism.L2.SG.Pf.phWellDef_holds X u`.
-/
theorem phase_well_defined_all_words : PhWellDefC := fun _ X _ u _ => Formalism.L2.SG.Pf.phWellDef_holds X u

end Formalism.L2.SG.Pf.RegroupPf
