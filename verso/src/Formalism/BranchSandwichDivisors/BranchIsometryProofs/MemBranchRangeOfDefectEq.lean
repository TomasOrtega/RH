import Formalism.BranchSandwichDivisors.StatementR

open Finset

namespace Formalism.BranchingDeterminantCap

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem memBranchRangeOfDefectEq : ConstituentRange := by
  unfold ConstituentRange
  intro n lam sg mu h1 h2 h3 i
  unfold Interlace at h1 h2
  have hmu := h2 i
  have hle : mu i - lam i.succ ≤ d0 lam mu := by
    unfold d0
    exact Finset.single_le_sum (f := fun j => mu j - lam j.succ)
      (fun j _ => sub_nonneg.mpr (h2 j).2) (Finset.mem_univ i)
  unfold rset
  rw [Finset.mem_Icc]
  refine ⟨hmu.2, le_min hmu.1 ?_⟩
  linarith

end Formalism.BranchingDeterminantCap
