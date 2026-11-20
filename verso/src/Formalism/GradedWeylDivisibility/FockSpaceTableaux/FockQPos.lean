import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `_ f g` and use `⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩`.
-/
theorem fischerInnerRatPos : FockQPos :=
  fun _ f g => ⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩

end Formalism.GradedWeylDivisibility
