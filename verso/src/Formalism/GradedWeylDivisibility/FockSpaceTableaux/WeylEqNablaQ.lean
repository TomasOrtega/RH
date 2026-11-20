import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem weylEqNablaQ_of (h : ClosedEqNabla) : WeylEqNablaQ := by
  intro r n hn ν hν
  refine h r n hn ν hν (weyl ℚ r n hn ν) (weylLeDual ℚ r n hn ν hν)
    (fun a b k f hf => weylRowDivStable ℚ r n hn ν a b k f hf) ?_

  exact Submodule.subset_span ⟨[], rfl⟩

end Formalism.GradedWeylDivisibility
