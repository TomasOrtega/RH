import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepClosedOf
import Formalism.FilteredPoleLength.LocalDescentLevels.LeadingTermLength

namespace Formalism.LatticeBaseChangeAlt

/- English proof (translation)
The claim follows from `localStepClosed_of leadingTermLength`.
-/
theorem localStepClosed : LocalStepClosed := localStepClosed_of leadingTermLength

end Formalism.LatticeBaseChangeAlt
