import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.CkModel
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.CkTwist

namespace PositivityTheory.RgFd

/- English proof (translation)
The claim follows from `coefPow_of CkM.ckModel ckTwist model_functions_multiply`.
-/
theorem coefPow : CoefPow := coefPow_of CkM.ckModel ckTwist model_functions_multiply

end PositivityTheory.RgFd
