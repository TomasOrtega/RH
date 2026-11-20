import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem column_degree_bound : CDge := by
  intro ℓ hℓ bi S η h hh
  have h2 : bi + S + η ≤ h + η := by omega
  gcongr
  all_goals first
    | exact_mod_cast h2
    | (rw [sub_nonneg]; exact_mod_cast (by omega : 1 ≤ ℓ))
    | (rw [sub_pos]; exact_mod_cast (by omega : 1 < ℓ))

end Formalism.KernelCokernelLengths
