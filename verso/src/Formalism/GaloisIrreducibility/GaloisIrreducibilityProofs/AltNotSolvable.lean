import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

/- English proof (translation)
Introduce `α _ _ h hA`. Establish `hcard : 5 ≤ Cardinal.mk α`. Rewrite using `[Cardinal.mk_fintype]`. Conclude with `h` after adjusting the coercions. Use `Equiv.Perm.not_isSolvable α hcard ?_` and prove the remaining obligations.

Conclude with `Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign (by rw [Subgroup.range_subtype]; exact le_rfl)`.
-/
theorem alternating_group_not_solvable : AltNotSolvable := by
  intro α _ _ h hA
  have hcard : 5 ≤ Cardinal.mk α := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast h
  refine Equiv.Perm.not_isSolvable α hcard ?_
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)

end Formalism.GaloisIrreducibility
