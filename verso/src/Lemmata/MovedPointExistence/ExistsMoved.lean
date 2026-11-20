import Mathlib

open Finset Matrix
open NormedSpace

namespace Bl.MovedPointExistence

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
private lemma exists_moved (σ : Equiv.Perm ι) (hσ : σ ≠ 1) (i : ι) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
    by_contra hc
    push Not at hc
    exact hσ (Equiv.ext fun x => by simpa using hc x)
  by_cases hi : σ i = i
  · refine ⟨k, ?_, hk⟩
    rintro rfl
    exact hk hi
  · refine ⟨σ i, hi, ?_⟩
    intro h2
    exact hi (σ.injective h2)

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem goal1 (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  have hfun : (fun t => (A t).det) =
      fun t => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' (A t)
  rw [hfun]
  have key : ∀ σ : Equiv.Perm ι,
      HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 := by
    intro σ
    exact (HasDerivAt.fun_finsetProd (u := univ) (fun i _ => h (σ i) i)).const_mul _
  have hs := HasDerivAt.fun_sum (u := univ) (fun σ _ => key σ)
  refine hs.congr_deriv ?_
  rw [h0, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp only [Matrix.trace, Matrix.diag_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one,
      one_mul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_one (fun j _ => ?_), one_mul]
    · rfl
    · rw [Equiv.Perm.one_apply, Matrix.one_apply_eq]
  · intro σ _ hσ
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    obtain ⟨j, hji, hj⟩ := exists_moved σ hσ i
    have hz : ∏ l ∈ univ.erase i, (1 : Matrix ι ι ℂ) (σ l) l = 0 :=
      Finset.prod_eq_zero (i := j) (by simp [hji]) (Matrix.one_apply_ne hj)
    rw [hz, zero_smul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

end Bl.MovedPointExistence
