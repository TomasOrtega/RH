import Formalism.GradedWeylDivisibility.StatementA
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `σ f g`. Conclude with `Formalism.REAL.fischerInner_eq_star g f`.
-/
theorem fischerInnerConjSymm_holds : FockHerm := by
  intro σ f g
  exact Formalism.REAL.fischerInner_eq_star g f

end Formalism.GradedWeylDivisibility
