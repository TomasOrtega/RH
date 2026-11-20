import Mathlib

namespace GlobalTheory.DetDerivativeAtOne

open Equiv Finset

/- English proof (translation)
Establish `hfun : (fun t : ℝ ↦ Matrix.det (A t)) = fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i`. Use function extensionality and compare the values at `fun t ↦ Matrix.det_apply' _`. Rewrite using `[hfun]`. Establish `hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i) (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0` using `fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)`. Establish `hsum` using `HasDerivAt.fun_sum (u := (univ : Finset (Perm n))) (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))`.

Use `hsum.congr_deriv (Eq.symm ?_)` and prove the remaining obligations. Rewrite using `[h0]`. Rewrite using `[Finset.sum_eq_single (1 : Perm n)]`. Simplify using `[Matrix.trace, Perm.one_apply, Matrix.one_apply]`. Introduce `σ _ hσ1`.

Establish `hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0`. Introduce `i`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, σ k ≠ k := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hσ1 (Equiv.ext hc)`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Apply `Finset.prod_eq_zero (i := σ k)` to reduce the goal to its premises. Simplify using `[hk]`.

Establish `: σ (σ k) ≠ σ k` using `fun h ↦ hk (σ.injective h)`. Simplify using `[Matrix.one_apply_ne this]`. Apply `Finset.prod_eq_zero (i := k)` to reduce the goal to its premises. Simplify using `[hki]`. Simplify using `[Matrix.one_apply_ne hk]`.

Simplify using `[hz]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hasDerivAt_det_of_one {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by
  have hfun : (fun t : ℝ ↦ Matrix.det (A t)) =
      fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t ↦ Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 :=
    fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))
  refine hsum.congr_deriv (Eq.symm ?_)
  rw [h0]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [Matrix.trace, Perm.one_apply, Matrix.one_apply]
  · intro σ _ hσ1
    have hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0 := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push Not at hc
        exact hσ1 (Equiv.ext hc)
      by_cases hki : k = i
      · subst hki
        apply Finset.prod_eq_zero (i := σ k)
        · simp [hk]
        · have : σ (σ k) ≠ σ k := fun h ↦ hk (σ.injective h)
          simp [Matrix.one_apply_ne this]
      · apply Finset.prod_eq_zero (i := k)
        · simp [hki]
        · simp [Matrix.one_apply_ne hk]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.DetDerivativeAtOne
