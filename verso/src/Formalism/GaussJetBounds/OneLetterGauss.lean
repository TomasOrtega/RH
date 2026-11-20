import Formalism.GaussJetBounds.GaussJetProofs.OneGauss
import Formalism.GaussJetBounds.GaussJetProofs.CoefficientBoundMembership
import Formalism.GaussJetBounds.GaussJetProofs.TheoremAMatrixEntries

namespace Formalism.DworkPowerSeriesWeights

/- English proof (translation)
The claim follows from `one_letter_gauss_sum`.
-/
theorem oneLetterGauss : OneLetterGauss := one_letter_gauss_sum
/- English proof (translation)
The claim follows from `theorem_A_matrix_entries`.
-/
theorem thmAEntry : ThmAEntry := theorem_A_matrix_entries

end Formalism.DworkPowerSeriesWeights
