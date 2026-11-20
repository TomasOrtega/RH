import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.OneLtNormXOfInKernel
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.JetsInOfOneVariable

namespace Formalism.L2.Th1.E

/- English proof (translation)
The claim follows from `shift_unit'`.
-/
theorem shiftUnit : ShiftUnit := shift_unit'
/- English proof (translation)
The claim follows from `shifted_points_integral`.
-/
theorem shiftPtsInt : ShiftPtsInt := shifted_points_integral

end Formalism.L2.Th1.E
