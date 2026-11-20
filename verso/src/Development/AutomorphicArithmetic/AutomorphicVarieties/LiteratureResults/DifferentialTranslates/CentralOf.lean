import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `E _ _ a M _ _ _ _ L q η h1 h2 X`. Set `o : Herm E a` to `⟨1, IsSelfAdjoint.one _⟩`. Establish `h` using `h2 (Fin.cons o X) 0 rfl`. Rewrite `h` using `[dCo_apply, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]`. Establish `e : Fin.removeNth (α` using `fun _ => Herm E a) 0 (Fin.cons o X) = X := by`.

Use function extensionality and compare the values at `j`. Simplify using `[Fin.removeNth]`. Rewrite `h` using `[e, Fin.val_zero, pow_zero, one_smul]`. Conclude with `h`. Introduce `i _`.

Establish `hz : η (Fin.removeNth (α` using `fun _ => Herm E a) i.succ (Fin.cons o X)) = 0 := by`. Consider the cases of `q with`. Consider the case `zero => exact i.elim0`. Consider the case `succ q`. Use `h1 _ 0 ?_` and prove the remaining obligations.

Simplify using `only [Fin.removeNth, Fin.succ_succAbove_zero, Fin.cons_zero]`. Both sides reduce to the same expression. Rewrite using `[hz, map_zero, smul_zero]`.
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
