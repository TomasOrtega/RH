import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ExtendedColumns

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT gtBox)

/- English proof (translation)
Introduce `m _ lam hlam Sg hSg`. Establish `hS : Sg = gtBox lam`. Use extensionality with `nu`. Rewrite using `[hSg, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i`. Conclude with `⟨(h.2 i).2, (h.2 i).1⟩`. Introduce `h`. Use `⟨Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox lam nu).2 h), fun i => ⟨(h i).2, (h i).1⟩⟩` and prove the remaining obligations. Rewrite using `[qk_dMu_eq_dGT (m + 1) lam hlam, hS]`.

Use `show ∑ κ ∈ gtBox lam, dGT m κ = _`. Use `sum_congr rfl fun nu hnu => ?_` and prove the remaining obligations. Rewrite using `[qk_dMu_eq_dGT m nu (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam hnu)]`.
-/
theorem branching_count_holds : CntBranch := by
  intro m _ lam hlam Sg hSg
  have hS : Sg = gtBox lam := by
    ext nu
    rw [hSg, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox]
    constructor
    · intro h i
      exact ⟨(h.2 i).2, (h.2 i).1⟩
    · intro h
      refine ⟨Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox lam nu).2 h), fun i => ⟨(h i).2, (h i).1⟩⟩
  rw [qk_dMu_eq_dGT (m + 1) lam hlam, hS]
  show ∑ κ ∈ gtBox lam, dGT m κ = _
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT m nu (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam hnu)]

end Formalism.InvariantFactorPaths.ColumnFamilies
