import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem RestPolynomialDecomposes.proof (h1 : RestPolynomialHomogeneousDecomposition.Statement) :
    RestPolynomialDecomposes.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, -⟩ := h1 f r a c
  exact ⟨Q, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
