import Formalism.PeriodIntegrals.QmSkip

namespace PI.QmSkipWork

/- English proof (translation)
Distinguish the cases in `h : k.val < p.val`. Rewrite using `[if_pos h, Fin.succAbove_of_castSucc_lt p k (by simpa [Fin.lt_def] using h)]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, Fin.succAbove_of_le_castSucc p k (by simp [Fin.le_def]; omega)]`. Simplify using the standard rewrite rules.
-/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt p k (by simpa [Fin.lt_def] using h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc p k (by simp [Fin.le_def]; omega)]
    simp

/- English proof (translation)
Unfold `PI.SkipSucc`. Introduce `t i j`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[PI.QmSkipWork.val_succAbove]`. Unfold `PI.skip1`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem skipSucc : PI.SkipSucc := by
  unfold PI.SkipSucc
  intro t i j
  apply Fin.ext
  rw [PI.QmSkipWork.val_succAbove]
  unfold PI.skip1
  split_ifs <;> rfl

/- English proof (translation)
Unfold `PI.SkipSucc2`. Introduce `t i i' j hii'`. Establish `hb : (i.succAbove i').val = i'.val + 1`. Rewrite using `[PI.QmSkipWork.val_succAbove, if_neg (by omega)]`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [PI.QmSkipWork.val_succAbove]`. Unfold `PI.skip2`. Apply the tactic sequence `split_ifs <;> (try dsimp only) <;> omega`.
-/
theorem skipSucc2 : PI.SkipSucc2 := by
  unfold PI.SkipSucc2
  intro t i i' j hii'
  have hb : (i.succAbove i').val = i'.val + 1 := by
    rw [PI.QmSkipWork.val_succAbove, if_neg (by omega)]
  apply Fin.ext
  simp only [PI.QmSkipWork.val_succAbove]
  unfold PI.skip2
  split_ifs <;> (try dsimp only) <;> omega

end PI.QmSkipWork
