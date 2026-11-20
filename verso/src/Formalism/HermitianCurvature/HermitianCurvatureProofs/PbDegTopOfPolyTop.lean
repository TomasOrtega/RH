import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfPartsAlt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtNormPow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JacquetRaisingOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbTopFirstOf

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `minor_cell_of_parts right_rule_derivative left_rule_cell torus_cell gauge_positivity`.
-/
theorem minor_cell : PBN.MinorCell :=
  minor_cell_of_parts right_rule_derivative left_rule_cell torus_cell gauge_positivity

/- English proof (translation)
The claim follows from `radial_raising_top_of_parts jacquet_raising_operator raising_cell minor_cell radial_side_raising raising_compact_support`.
-/
theorem radial_raising_top : PBN.RadAATop :=
  radial_raising_top_of_parts jacquet_raising_operator raising_cell minor_cell radial_side_raising raising_compact_support

/- English proof (translation)
The claim follows from `pb_degTop_of radial_raising_top hPT`.
-/
theorem pb_degTop_of_polyTop (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop := pb_degTop_of radial_raising_top hPT

end Formalism.FourierDecayAlt.P
