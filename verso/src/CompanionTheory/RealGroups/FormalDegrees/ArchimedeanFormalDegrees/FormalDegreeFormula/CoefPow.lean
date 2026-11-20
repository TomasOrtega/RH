import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CkModel
import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CkTwist

namespace CompanionTheory.RgFd

/- English proof (translation)
The claim follows from `coefPow_of CkM.ckModel ckTwist model_functions_multiply`.
-/
theorem coefPow : CoefPow := coefPow_of CkM.ckModel ckTwist model_functions_multiply

end CompanionTheory.RgFd
