import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeTheoremOfDischarge
import Formalism.PolynomialDimension.FinalM

namespace Formalism.InvariantFactorPaths.PW.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_theorem_height_bound : LatticeTheoremHeightBound := lattice_theorem_of_discharge Formalism.CountingSumsFrames.Top.theoremM discharge_height_bound

end Formalism.InvariantFactorPaths.PW.Top
