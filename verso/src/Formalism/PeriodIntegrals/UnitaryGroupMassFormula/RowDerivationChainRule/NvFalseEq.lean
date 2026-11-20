import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer

open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

/- English proof (translation)
Simplify using `[Nv, Matrix.adjugate_apply]`.
-/
theorem Nv_false_eq (K : Type) [Field K] (m : ℕ) (c : Fin (m + 1)) :
    Nv K m false c = ((genM K m).updateRow c (Pi.single (Fin.last m) 1)).det := by
  simp [Nv, Matrix.adjugate_apply]

/- English proof (translation)
Introduce `K _ m a b c`. Establish `hN : ∀ d, Nv K m false d = ((genM K m).updateRow d (Pi.single (Fin.last m) 1)).det` using `fun d => Nv_false_eq K m d`. Establish `hG : ∀ i j, genM K m i j = X (i, j)` using `fun i j => rfl`. Rewrite using `[RE_eq_REder, hN c, hN b, derivation_det]`. Establish `hrow : ∀ i j, REder K (m + 1) a b (((genM K m).updateRow c (Pi.single (Fin.last m) 1)) i j) = if i = c then 0 else if i = b then X (a, j) else 0`.

Introduce `i j`. Distinguish the cases in `hic : i = c`. Substitute `hic` using the available equality. Rewrite using `[Matrix.updateRow_self, if_pos rfl]`. Distinguish the cases in `hj : j = Fin.last m`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Rewrite using `[Matrix.updateRow_ne hic, hG, REder_X, if_neg hic]`. Repeatedly rewrite using `[hrow]`.

Establish `hz : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) (i : Fin (m + 1)) (r : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), (∀ j, r j = 0) → (M.updateRow i r).det = 0`. Introduce `M i r hr`. Conclude with `Matrix.det_eq_zero_of_row_eq_zero i (fun j => by rw [Matrix.updateRow_self]; exact hr j)`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality.

Rewrite using `[Finset.sum_eq_zero]`. Simplify using the standard rewrite rules. Introduce `i _`. Apply `hz` to reduce the goal to its premises. Introduce `j`.

Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[Finset.sum_eq_single b]`. Use `rotate_left`. Introduce `i _ hib`. Apply `hz` to reduce the goal to its premises.

Introduce `j`. Apply the tactic sequence `split_ifs <;> rfl`. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`. Simplify using `only [hbc, if_false, if_true, eq_self_iff_true, ite_true, ite_false]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_neg hbc, sub_zero]`. Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Distinguish the cases in `hi : i = a`. Rewrite using `[hi, Matrix.updateRow_self]`. Simplify using `only [Matrix.updateRow_apply, hG]`. Apply the tactic sequence `try (split_ifs <;> simp_all)`. Rewrite using `[Matrix.updateRow_ne hi]`.

Rewrite using `[if_neg hab]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Rewrite using `[if_pos rfl, zero_sub]`. Establish `hperm : (((genM K m).updateRow a (Pi.single (Fin.last m) 1)).updateRow b (fun j => X (a, j))) = ((genM K m).updateRow b (Pi.single (Fin.last m) 1)).submatrix (Equiv.swap b a) id`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply, id, Matrix.updateRow_apply, Equiv.swap_apply_def, hG]`. Apply the tactic sequence `split_ifs <;> simp_all`. Rewrite using `[hperm, Matrix.det_permute, Equiv.Perm.sign_swap hbc]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hac, sub_zero]`. Apply `Matrix.det_zero_of_row_eq hab` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Rewrite using `[Matrix.updateRow_ne hab, Matrix.updateRow_self, Matrix.updateRow_ne hac, hG]`.
-/
theorem keyCov : KeyCov := by
  intro K _ m a b c
  have hN : ∀ d, Nv K m false d =
      ((genM K m).updateRow d (Pi.single (Fin.last m) 1)).det := fun d => Nv_false_eq K m d
  have hG : ∀ i j, genM K m i j = X (i, j) := fun i j => rfl
  rw [RE_eq_REder, hN c, hN b, derivation_det]
  have hrow : ∀ i j, REder K (m + 1) a b
      (((genM K m).updateRow c (Pi.single (Fin.last m) 1)) i j) =
        if i = c then 0 else if i = b then X (a, j) else 0 := by
    intro i j
    by_cases hic : i = c
    · subst hic
      rw [Matrix.updateRow_self, if_pos rfl]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · rw [Matrix.updateRow_ne hic, hG, REder_X, if_neg hic]
  simp_rw [hrow]
  have hz : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (i : Fin (m + 1)) (r : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
      (∀ j, r j = 0) → (M.updateRow i r).det = 0 := by
    intro M i r hr
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by rw [Matrix.updateRow_self]; exact hr j)
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      apply hz
      intro j
      split_ifs <;> rfl
  rw [Finset.sum_eq_single b]
  rotate_left
  · intro i _ hib
    apply hz
    intro j
    split_ifs <;> rfl
  · intro h; exact absurd (Finset.mem_univ b) h
  simp only [hbc, if_false, if_true, eq_self_iff_true, ite_true, ite_false]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg hbc, sub_zero]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases hi : i = a
    · rw [hi, Matrix.updateRow_self]
      simp only [Matrix.updateRow_apply, hG]
      try (split_ifs <;> simp_all)
    · rw [Matrix.updateRow_ne hi]
  rw [if_neg hab]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, zero_sub]
    have hperm : (((genM K m).updateRow a (Pi.single (Fin.last m) 1)).updateRow b
        (fun j => X (a, j))) =
        ((genM K m).updateRow b (Pi.single (Fin.last m) 1)).submatrix (Equiv.swap b a) id := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.submatrix_apply, id, Matrix.updateRow_apply, Equiv.swap_apply_def, hG]
      split_ifs <;> simp_all
    rw [hperm, Matrix.det_permute, Equiv.Perm.sign_swap hbc]
    simp
  · rw [if_neg hac, sub_zero]
    apply Matrix.det_zero_of_row_eq hab
    funext j
    rw [Matrix.updateRow_ne hab, Matrix.updateRow_self, Matrix.updateRow_ne hac, hG]

end PI.RL.W
