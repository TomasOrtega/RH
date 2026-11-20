import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.MemSpanStandardIffProjZero

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

/- English proof (translation)
Introduce `hA n _ M CF pi hpi` and use `qb_Mpi_eq hA CF pi hpi`.
-/
theorem filtration_standard_span_of : LemmaA → FiltrationStandardSpan :=
  fun hA n _ M CF pi hpi => qb_Mpi_eq hA CF pi hpi

end Formalism.InvariantFactorPaths.ColumnFamilies
