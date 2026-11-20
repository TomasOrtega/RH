import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.AntitoneOfMemGtBox
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Branch
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.NormIndexCountBound

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

/- English proof (translation)
Use `first`. Consider the case `exact stripsMem_proof`. Consider the case `exact P.stripsMem_proof`. Consider the case `exact strips_mem`. Consider the case `exact P.strips_mem`.

Consider the case `exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.stripsMem_proof`. Consider the case `exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.strips_mem`.
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
Use `first`. Consider the case `exact gtPieri_proof`. Consider the case `exact P.gtPieri_proof`. Consider the case `exact gelfand_tsetlin_pieri`. Consider the case `exact P.gelfand_tsetlin_pieri`.

Consider the case `exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.gtPieri_proof`. Consider the case `exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.gelfand_tsetlin_pieri`.
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
Use `first`. Consider the case `exact stdCountGT_proof`. Consider the case `exact P.stdCountGT_proof`. Consider the case `exact standard_count_gt`. Consider the case `exact P.standard_count_gt`.

Consider the case `exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.stdCountGT_proof`. Consider the case `exact Formalism.InvariantFactorPaths.GelfandTsetlinBases.P.standard_count_gt`.
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
The claim follows from `countCont_of stripsMem gtPieri stdCountGT`.
-/
theorem countCont : CountCont := countCont_of stripsMem gtPieri stdCountGT
/- English proof (translation)
The claim follows from `countPAll_of countCont`.
-/
theorem countPAll : CountPAll := countPAll_of countCont

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
