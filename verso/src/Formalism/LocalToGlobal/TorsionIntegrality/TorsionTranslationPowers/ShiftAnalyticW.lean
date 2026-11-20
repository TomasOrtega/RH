import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW

namespace Formalism.L2.Th1.E

/- English proof (translation)
The claim follows from `analytic_point_eq_zero_iff`.
-/
theorem ptWZero : PtWZero := analytic_point_eq_zero_iff
/- English proof (translation)
The claim follows from `analytic_point_map_add`.
-/
theorem ptWAdd : PtWAdd := analytic_point_map_add
/- English proof (translation)
The claim follows from `shift_analytic_model`.
-/
theorem shiftAnalyticW : ShiftAnalyticW := shift_analytic_model

end Formalism.L2.Th1.E
