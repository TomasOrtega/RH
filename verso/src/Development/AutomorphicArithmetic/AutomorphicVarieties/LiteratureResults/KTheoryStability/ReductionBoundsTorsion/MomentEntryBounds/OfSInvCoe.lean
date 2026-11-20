import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SubLeSumAbsConsecutiveDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OneLeAbsNorm

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mul (x y : Sp L N) (w : InfinitePlace L) : mt (x * y) w = mt x w * mt y w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_one (w : InfinitePlace L) : mt (1 : Sp L N) w = 1 := rfl

/- English proof (translation)
Rewrite using `[← mt_mul, inv_mul_cancel, mt_one]`.
-/
theorem mt_inv_mul (x : Sp L N) (w : InfinitePlace L) : mt x⁻¹ w * mt x w = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

/- English proof (translation)
Rewrite using `[← mt_mul, mul_inv_cancel, mt_one]`.
-/
theorem mt_mul_inv (x : Sp L N) (w : InfinitePlace L) : mt x w * mt x⁻¹ w = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

/- English proof (translation)
Rewrite using `[← Pi.inv_apply, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem ofS_inv_coe (x : Sp L N) (w : InfinitePlace L) :
    ((((ofS L N x) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = mt x⁻¹ w := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

/- English proof (translation)
Simplify using `only [q, qR]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w`. Simplify using `only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]`. Rewrite using `[hm, re_quad]`.
-/
theorem q_actL (x : Sp L N) (y : Lat L N) :
    q (actL (ofS L N x) (one L N).1) y = ∑ w, ∑ i, ‖(mt x⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  rw [hm, re_quad]

/- English proof (translation)
Simplify using `only [q, qR]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hBM : mt x⁻¹ w * mt x w = 1` using `mt_inv_mul x w`. Establish `hMB : mt x w * mt x⁻¹ w = 1` using `mt_mul_inv x w`. Establish `hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w`.

Simplify using `only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]`. Establish `hinv : (mat (actL (ofS L N x) (one L N).1) w)⁻¹ = mt x w * (mt x w)ᴴ`. Rewrite using `[hm]`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hBM, Matrix.conjTranspose_one, Matrix.mul_one, hMB]`. Establish `hd : mat (dualH (actL (ofS L N x) (one L N).1)) w = ((mt x w)ᵀ)ᴴ * (mt x w)ᵀ`. Simplify using `only [dualH, mat_mkHS]`.

Rewrite using `[hinv, Matrix.transpose_mul]`. Both sides reduce to the same expression. Rewrite using `[hd, re_quad]`.
-/
theorem q_dual (x : Sp L N) (y : Lat L N) :
    q (dualH (actL (ofS L N x) (one L N).1)) y = ∑ w, ∑ i, ‖((mt x w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hBM : mt x⁻¹ w * mt x w = 1 := mt_inv_mul x w
  have hMB : mt x w * mt x⁻¹ w = 1 := mt_mul_inv x w
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  have hinv : (mat (actL (ofS L N x) (one L N).1) w)⁻¹ = mt x w * (mt x w)ᴴ := by
    rw [hm]
    refine Matrix.inv_eq_left_inv ?_
    calc mt x w * (mt x w)ᴴ * ((mt x⁻¹ w)ᴴ * mt x⁻¹ w)
        = mt x w * (mt x⁻¹ w * mt x w)ᴴ * mt x⁻¹ w := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBM, Matrix.conjTranspose_one, Matrix.mul_one, hMB]
  have hd : mat (dualH (actL (ofS L N x) (one L N).1)) w = ((mt x w)ᵀ)ᴴ * (mt x w)ᵀ := by
    simp only [dualH, mat_mkHS]
    rw [hinv, Matrix.transpose_mul]
    rfl
  rw [hd, re_quad]

/- English proof (translation)
Establish `hne : Nonempty {y : Lat L N // y ≠ 0}`. Use `⟨⟨fun _ => 1, fun h0 => ?_⟩⟩` and prove the remaining obligations. Use `congrFun h0 ⟨0, hN⟩` as an intermediate fact. Conclude with `one_ne_zero this`. Unfold `lam`.

Conclude with `le_ciInf fun y => hκ y.1 y.2`.
-/
theorem lam_ge (hN : 1 ≤ N) {h : HS L N} {κ : ℝ} (hκ : ∀ y : Lat L N, y ≠ 0 → κ ≤ q h y) : κ ≤ lam h := by
  have hne : Nonempty {y : Lat L N // y ≠ 0} := by
    refine ⟨⟨fun _ => 1, fun h0 => ?_⟩⟩
    have := congrFun h0 ⟨0, hN⟩
    exact one_ne_zero this
  unfold lam
  exact le_ciInf fun y => hκ y.1 y.2

end PositivityTheory.KB.MomentRationality.Ht
