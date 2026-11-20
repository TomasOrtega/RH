import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell

namespace Formalism.QuantumDeterminants

/- English proof (translation)
The claim follows from `big_cell_mem_holds`.
-/
theorem bigCellMem : BigCellMem := big_cell_mem_holds
/- English proof (translation)
The claim follows from `big_cell_coordinate_holds`.
-/
theorem bigCellZhat : BigCellZhat := big_cell_coordinate_holds
/- English proof (translation)
The claim follows from `big_cell_minors_holds`.
-/
theorem bigCellMinors : BigCellMinors := big_cell_minors_holds

end Formalism.QuantumDeterminants
