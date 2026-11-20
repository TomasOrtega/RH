import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.GenFrameSBOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.StepBack
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.SatProj

namespace GenFrameSpan

/- English proof (translation)
The claim follows from `stepSat_of projZ`.
-/
theorem stepSat : StepSat := stepSat_of projZ

/- English proof (translation)
The claim follows from `genFrameSB_of stepBack hs stepSat`.
-/
theorem genFrameSB_of_span (hs : StepSpan) : CutKW.KWsb := genFrameSB_of stepBack hs stepSat

end GenFrameSpan
