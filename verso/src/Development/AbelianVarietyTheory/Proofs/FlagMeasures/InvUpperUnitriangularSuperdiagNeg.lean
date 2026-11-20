import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hA : A.BlockTriangular id` using `fun i j h => hlow i j h`. Establish `hdet : A.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular hA]`. Simplify using `[hdiag]`. Use `haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (by rw [hdet]; exact isUnit_one)`.

Establish `hB : (A⁻¹).BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hA`. Establish `hlowB : ∀ x y : Fin n, y < x → A⁻¹ x y = 0` using `fun x y h => hB h`. Establish `hmul : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one)`. Establish `hdiagB : ∀ x, A⁻¹ x x = 1`. Introduce `x`.

Establish `h` using `congrFun (congrFun hmul x) x`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single x]`. Simplify `h` using `[hdiag]`. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with hj | hj` into its components or cases.

Rewrite using `[hlow x j hj, zero_mul]`. Rewrite using `[hlowB j x hj, mul_zero]`. Simplify using the standard rewrite rules. Use `⟨hlowB, hdiagB, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`.

Establish `hxy' : x < y`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Establish `h` using `congrFun (congrFun hmul x) y`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hxy'), Finset.sum_eq_add (x) (y) (ne_of_lt hxy')]`.

Rewrite `h` using `[hdiag x, hdiagB y, one_mul, mul_one]`. Conclude with `eq_neg_of_add_eq_zero_left h`. Introduce `j _ hj`. Break down `lt_trichotomy j x with h1 | h1 | h1` into its components or cases. Rewrite using `[hlow x j h1, zero_mul]`.

Conclude with `absurd h1 hj.1`. Establish `: y < j`. Break down `lt_trichotomy j y with h2 | h2 | h2` into its components or cases. It suffices to derive a contradiction. Rewrite `h1`, `h2` using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers. Conclude with `absurd h2 hj.2`. Conclude with `h2`. Rewrite using `[hlowB j y this, mul_zero]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem inv_upperUnitriangular (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k)
    (hlow : ∀ x y : Fin n, y < x → A x y = 0) (hdiag : ∀ x, A x x = 1) :
    (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧
      ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  have hA : A.BlockTriangular id := fun i j h => hlow i j h
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    simp [hdiag]
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (by rw [hdet]; exact isUnit_one)
  have hB : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hlowB : ∀ x y : Fin n, y < x → A⁻¹ x y = 0 := fun x y h => hB h
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one)
  have hdiagB : ∀ x, A⁻¹ x x = 1 := by
    intro x
    have h := congrFun (congrFun hmul x) x
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single x] at h
    · simpa [hdiag] using h
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hlow x j hj, zero_mul]
      · rw [hlowB j x hj, mul_zero]
    · simp
  refine ⟨hlowB, hdiagB, ?_⟩
  intro x y hxy
  have hxy' : x < y := by
    rw [Fin.lt_def]; omega
  have h := congrFun (congrFun hmul x) y
  rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hxy'),
    Finset.sum_eq_add (x) (y) (ne_of_lt hxy')] at h
  · rw [hdiag x, hdiagB y, one_mul, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro j _ hj
    rcases lt_trichotomy j x with h1 | h1 | h1
    · rw [hlow x j h1, zero_mul]
    · exact absurd h1 hj.1
    · have : y < j := by
        rcases lt_trichotomy j y with h2 | h2 | h2
        · exfalso; rw [Fin.lt_def] at h1 h2; omega
        · exact absurd h2 hj.2
        · exact h2
      rw [hlowB j y this, mul_zero]
  · simp
  · simp

end GlobalTheory
