import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem centralOf : CentralOf := by
  intro E _ _ a M _ _ _ _ L q η h1 h2 X
  let o : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have h := h2 (Fin.cons o X) 0 rfl
  rw [dCo_apply, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero] at h
  · have e : Fin.removeNth (α := fun _ => Herm E a) 0 (Fin.cons o X) = X := by
      funext j; simp [Fin.removeNth]
    rw [e, Fin.val_zero, pow_zero, one_smul] at h
    exact h
  · intro i _
    have hz : η (Fin.removeNth (α := fun _ => Herm E a) i.succ (Fin.cons o X)) = 0 := by
      cases q with
      | zero => exact i.elim0
      | succ q =>
        refine h1 _ 0 ?_
        simp only [Fin.removeNth, Fin.succ_succAbove_zero, Fin.cons_zero]
        rfl
    rw [hz, map_zero, smul_zero]

end UpperTheory.V.Lit.Dr
