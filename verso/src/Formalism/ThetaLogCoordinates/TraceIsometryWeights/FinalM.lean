import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeTheoremOfDischarge
import Formalism.PolynomialDimension.FinalM

namespace Formalism.InvariantFactorPaths.PW.Top

/- English proof (translation)
The claim follows from `lattice_theorem_of_discharge Formalism.CountingSumsFrames.Top.theoremM discharge_height_bound`.
-/
theorem lattice_theorem_height_bound : LatticeTheoremHeightBound := lattice_theorem_of_discharge Formalism.CountingSumsFrames.Top.theoremM discharge_height_bound

end Formalism.InvariantFactorPaths.PW.Top
