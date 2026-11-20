import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.AntitoneOfMemGtBox
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Branch
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem stripsMem : StripsMem := by
  first
  | exact stripsMem_proof
  | exact P.stripsMem_proof
  | exact strips_mem
  | exact P.strips_mem
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.stripsMem_proof
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.strips_mem
/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem gtPieri : GTPieri := by
  first
  | exact gtPieri_proof
  | exact P.gtPieri_proof
  | exact gelfand_tsetlin_pieri
  | exact P.gelfand_tsetlin_pieri
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.gtPieri_proof
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.gelfand_tsetlin_pieri
/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem stdCountGT : StdCountGT := by
  first
  | exact stdCountGT_proof
  | exact P.stdCountGT_proof
  | exact standard_count_gt
  | exact P.standard_count_gt
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.stdCountGT_proof
  | exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.standard_count_gt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countCont : CountCont := countCont_of stripsMem gtPieri stdCountGT
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countPAll : CountPAll := countPAll_of countCont

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
