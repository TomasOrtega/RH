import Formalism.GradedWeylDivisibility.StatementC

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `h r n ν _`. Conclude with `h ℤ r n ν`.
-/
theorem standardMonomialSpanOf : StandardMonomialSpanOf := by
  intro h r n ν _
  exact h ℤ r n ν

end Formalism.GradedWeylDivisibility
