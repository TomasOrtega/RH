import Mathlib

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Assume the negation of the conclusion and derive a contradiction.

A detailed English derivation is pending.
-/
private theorem UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne {a : ℕ} {σ : Equiv.Perm (Fin a)} (hσ : σ ≠ 1)
    (i : Fin a) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  ext1 j
  by_cases hj : j = i
  · subst hj
    by_contra hne
    exact hne (σ.injective (h _ hne))
  · exact h j hj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det :
    ∀ {a : ℕ} {m : ℝ → Matrix (Fin a) (Fin a) ℂ}
    {Y : Matrix (Fin a) (Fin a) ℂ},
    m (0 : ℝ) = (1 : Matrix (Fin a) (Fin a) ℂ) →
      (∀ (i j : Fin a), HasDerivAt (fun (s : ℝ) ↦ m s i j) (Y i j) (0 : ℝ)) →
        HasDerivAt (fun (s : ℝ) ↦ (m s).det) (∑ i : Fin a, Y i i) (0 : ℝ) := by
  intro a m Y h0 hd
  have key : HasDerivAt
      (fun s : ℝ ↦ ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, m s (σ i) i)
      (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) 0 :=
    HasDerivAt.fun_sum fun σ _ ↦
      (HasDerivAt.fun_finsetProd (f := fun i s ↦ m s (σ i) i)
        (fun i _ ↦ hd (σ i) i)).const_mul _
  have hval : (∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, m 0 (σ j) j) • Y (σ i) i) = ∑ i, Y i i := by
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin a))]
    · simp [h0]
    · intro σ _ hσ
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
      obtain ⟨j, hj, hm⟩ := UpperTheory.Reformulated.B.MovedPointDeterminant.exists_moved_ne hσ i
      rw [Finset.prod_eq_zero (i := j) (by simp [hj]) (by rw [h0, Matrix.one_apply_ne hm]),
        zero_smul]
    · simp
  rw [hval] at key
  simpa only [Matrix.det_apply'] using key
