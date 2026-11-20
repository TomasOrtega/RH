import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem dualWeylModuleMul : DualWeylMul := fun _ _ _ _ _ _ _ _ =>
  ⟨fun hf hg => dualWeyl_mul hf hg, one_mem_dualWeyl⟩

end Formalism.GradedWeylDivisibility
