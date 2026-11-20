import Mathlib

namespace Bl.b110

/- English proof (translation)
Distinguish the cases in `hi : σ i = i`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, σ k ≠ k := by`. Assume the negation of the conclusion as `h`. Conclude with `hσ (Equiv.ext fun k => not_not.mp fun hk => h ⟨k, hk⟩)`. Use `⟨k, ?_, hk⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `hk hi`. Use `⟨σ i, hi, ?_⟩` and prove the remaining obligations. Introduce `h`. Conclude with `hi (σ.injective h)`.
-/
private lemma exists_moved {n : Type} [DecidableEq n] (σ : Equiv.Perm n) (hσ : σ ≠ 1) (i : n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_cases hi : σ i = i
  · obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra h
      exact hσ (Equiv.ext fun k => not_not.mp fun hk => h ⟨k, hk⟩)
    refine ⟨k, ?_, hk⟩
    rintro rfl
    exact hk hi
  · refine ⟨σ i, hi, ?_⟩
    intro h
    exact hi (σ.injective h)

/- English proof (translation)
Introduce `n _ _ A A' h0 hd`. Establish `hfun : (fun t : ℝ => Matrix.det (A t)) = fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i`. Use function extensionality and compare the values at `t`. Conclude with `Matrix.det_apply' _`. Rewrite using `[hfun]`.

Establish `hprod : ∀ σ : Equiv.Perm n, HasDerivAt (fun t : ℝ => ∏ i, A t (σ i) i) (∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0`. Introduce `σ`. Conclude with `HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i) (fun i _ => hd (σ i) i)`. Establish `hsum` using `HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => (hprod σ).const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)))`. Use `hsum.congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single (1 : Equiv.Perm n)]`. Simplify using `only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply, h0, smul_eq_mul, Matrix.trace]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_one, one_mul]`. Both sides reduce to the same expression.

Introduce `j _`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Rewrite using `[Finset.sum_eq_zero, mul_zero]`. Introduce `i _`.

Take `⟨j, hji, hj⟩` from `exists_moved σ hσ i`. Rewrite using `[Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩), zero_smul]`. Rewrite using `[h0]`. Conclude with `Matrix.one_apply_ne hj`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem goal1 :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by
  intro n _ _ A A' h0 hd
  have hfun : (fun t : ℝ => Matrix.det (A t)) =
      fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' _
  rw [hfun]
  have hprod : ∀ σ : Equiv.Perm n, HasDerivAt (fun t : ℝ => ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 := by
    intro σ
    exact HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i)
      (fun i _ => hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun σ _ => (hprod σ).const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)))
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply,
      h0, smul_eq_mul, Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.prod_eq_one, one_mul]
    · rfl
    intro j _
    simp
  · intro σ _ hσ
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    obtain ⟨j, hji, hj⟩ := exists_moved σ hσ i
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩), zero_smul]
    rw [h0]
    exact Matrix.one_apply_ne hj
  · intro h
    exact absurd (Finset.mem_univ _) h

end Bl.b110
