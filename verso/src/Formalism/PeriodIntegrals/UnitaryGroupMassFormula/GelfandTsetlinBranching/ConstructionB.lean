import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RenameTauHomogB

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
The claim follows from `stableCompl_B`.
-/
theorem stable_complement_exists : StableCompl := stableCompl_B

/- English proof (translation)
The claim follows from `highestVec_B`.
-/
theorem highest_weight_vector_exists : HighestVec := highestVec_B

end PI.WGB
