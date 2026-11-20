import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `_ f f' g c` and use `⟨lfockq_add_left f f' g, lfockq_smul_left c f g⟩`.
-/
theorem fischerInnerRatBilinear : FockQBilin := fun _ f f' g c =>
  ⟨lfockq_add_left f f' g, lfockq_smul_left c f g⟩

end Formalism.GradedWeylDivisibility
