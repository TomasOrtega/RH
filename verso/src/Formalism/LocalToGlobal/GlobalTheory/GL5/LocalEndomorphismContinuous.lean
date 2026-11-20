import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocalEnd
import Formalism.LocalToGlobal.GlobalTheory.GL5.LevelsProGOfSplitAlgebra

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
The claim follows from `local_endomorphism_homeomorph`.
-/
theorem local_endomorphism_continuous : ProGW.LocalEndHomeo := local_endomorphism_homeomorph

/- English proof (translation)
The claim follows from `ProGW.levels_pro_g_of_continuity local_endomorphism_continuous`.
-/
theorem levels_pro_g : Link4p := ProGW.levels_pro_g_of_continuity local_endomorphism_continuous

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
