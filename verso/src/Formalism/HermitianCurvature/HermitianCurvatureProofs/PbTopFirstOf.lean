import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeNormPower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `degree_top_of_parts word_recursion hRA hPT density_constant`.
-/
theorem pb_degTop_of (hRA : PBN.RadAATop) (hPT : PBN.PolyTop) : Formalism.FourierDecayAlt.KB.DegTop :=
  degree_top_of_parts word_recursion hRA hPT density_constant

end Formalism.FourierDecayAlt.P
