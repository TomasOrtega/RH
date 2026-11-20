import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2

/- English proof (translation)
Establish `hsa : ∀ {n : ℕ} (p : Fin (n + 1)) (k : Fin n), (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1`. Introduce `n p k`. Unfold `Fin.succAbove`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]`. Use `⟨fun t i j => ?_, fun t i i' j hii' => ?_⟩` and prove the remaining obligations.

Apply `Fin.ext` to reduce the goal to its premises. Establish `e` using `hsa i j`. Unfold `PI.skip1`. Apply the tactic sequence `split_ifs at e ⊢ <;> simp only at * <;> omega`. Apply `Fin.ext` to reduce the goal to its premises.

Establish `e1` using `hsa i i'`. Establish `e2` using `hsa i' j`. Establish `e3` using `hsa i (i'.succAbove j)`. Rewrite `e1` using `[if_neg (by omega)]`. Unfold `PI.skip2`.

Apply the tactic sequence `split_ifs at e2 e3 ⊢ <;> simp only at * <;> omega`.
-/
theorem quantum_minor_skip : PI.QmSkip := by
  have hsa : ∀ {n : ℕ} (p : Fin (n + 1)) (k : Fin n),
      (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
    intro n p k
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
  refine ⟨fun t i j => ?_, fun t i i' j hii' => ?_⟩
  · apply Fin.ext
    have e := hsa i j
    unfold PI.skip1
    split_ifs at e ⊢ <;> simp only at * <;> omega
  · apply Fin.ext
    have e1 := hsa i i'
    have e2 := hsa i' j
    have e3 := hsa i (i'.succAbove j)
    rw [if_neg (by omega)] at e1
    unfold PI.skip2
    split_ifs at e2 e3 ⊢ <;> simp only at * <;> omega
