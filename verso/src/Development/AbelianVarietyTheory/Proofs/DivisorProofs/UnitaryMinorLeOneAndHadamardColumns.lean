import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent

open scoped Matrix

namespace GlobalTheory.UnitaryMinor

/- English proof (translation)
Establish `h` using `congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 u.2) j) j`. Simplify using `only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h`. Establish `h2 : ((∑ i, ‖u.1 i j‖ ^ 2 : ℝ) : ℂ) = 1`. Rewrite using `[← h]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Conclude with `h2` after adjusting the coercions.
-/
theorem sum_norm_sq_col {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, ‖u.1 i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 u.2) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ i, ‖u.1 i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast h2

/- English proof (translation)
Distinguish the cases in `hI : Function.Injective I`. Establish `h : ‖(u.1.submatrix I J).det‖ ^ 2 ≤ 1`. Use `(GlobalTheory.Hadamard.norm_det_sq_le_prod_col (u.1.submatrix I J)).trans ?_` and prove the remaining obligations. Use `Finset.prod_le_one (fun j _ => Finset.sum_nonneg fun _ _ => by positivity) fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_norm_sq_col u (J j)]`.

Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := I) (f := fun i => ‖u.1 i (J j)‖ ^ 2) (fun a _ b _ h => hI h)]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity`. Conclude with `(sq_le_one_iff₀ (norm_nonneg _)).1 h`. Take `⟨a, b, hab, hne⟩` from `Function.not_injective_iff.1 hI`.

Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext k; simp [hab])]`. Simplify using the standard rewrite rules.
-/
theorem norm_det_submatrix_le_one (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (I J : Fin s → Fin n) : ‖(u.1.submatrix I J).det‖ ≤ 1 := by
  by_cases hI : Function.Injective I
  · have h : ‖(u.1.submatrix I J).det‖ ^ 2 ≤ 1 := by
      refine (GlobalTheory.Hadamard.norm_det_sq_le_prod_col (u.1.submatrix I J)).trans ?_
      refine Finset.prod_le_one (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
        fun j _ => ?_
      rw [← sum_norm_sq_col u (J j)]
      simp only [Matrix.submatrix_apply]
      rw [← Finset.sum_image (s := Finset.univ) (g := I) (f := fun i => ‖u.1 i (J j)‖ ^ 2)
        (fun a _ b _ h => hI h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => by positivity
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hI
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hab])]
    simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨norm_det_submatrix_le_one, fun _ _ _ M => GlobalTheory.Hadamard.norm_det_sq_le_prod_col M⟩`.
-/
theorem unitary_minor_and_hadamard :
    (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n),
      ‖(u.1.submatrix I J).det‖ ≤ 1) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 :=
  ⟨norm_det_submatrix_le_one, fun _ _ _ M => GlobalTheory.Hadamard.norm_det_sq_le_prod_col M⟩

end GlobalTheory.UnitaryMinor
