import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths

/- English proof (translation)
Unfold `RowD`. Introduce `h h1 η hη`. Establish `key : 32 * (h1 + η) ≤ 50 * h1` using `by omega`. Use `gcongr ?_ / _`. Conclude with `key` after adjusting the coercions.
-/
theorem row_degree_bound : RowD := by
  unfold RowD
  intro h h1 η hη
  have key : 32 * (h1 + η) ≤ 50 * h1 := by omega
  gcongr ?_ / _
  exact_mod_cast key

end Formalism.KernelCokernelLengths
