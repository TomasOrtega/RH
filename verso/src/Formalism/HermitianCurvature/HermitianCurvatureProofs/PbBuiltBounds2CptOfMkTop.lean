import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfHeadTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOfMkTop

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)`.
-/
theorem pb_builtBounds2Cpt_of_mkTop (hM : CutEX.MkTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)

end Formalism.FourierDecayAlt.P
