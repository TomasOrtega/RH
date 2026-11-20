import Mathlib
import ReciprocityTheory.SemistableReduction.LatAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfA

open Matrix MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory

/- English proof (translation)
Introduce `p x hx`. Establish `hM : ∀ k : Fin (p + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor x k ≠ 0`. Introduce `k`. Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations. Unfold `ReciprocityTheory.ChartRestriction.G.FD.lminor`.

Establish `: IsEmpty (Fin ((0 : Fin (p + 1)) : ℕ))` using `inferInstanceAs (IsEmpty (Fin 0))`. Rewrite using `[Matrix.det_isEmpty]`. Conclude with `one_ne_zero`. Conclude with `hx i`. Use `set L := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm x with hL`.

Establish `hu : IsUnit L.det`. Rewrite using `[hL, ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_det]`. Conclude with `isUnit_one`. Establish `hup : ∀ i k : Fin p, i < k → L i k = 0` using `ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_up x`. Establish `hd : ∀ i : Fin p, L i i = 1` using `ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diag x`.

Establish `hbt : L.BlockTriangular OrderDual.toDual` using `fun i k h => hup i k h`. Set `: Invertible L` to `L.invertibleOfIsUnitDet hu`. Establish `hinv : L⁻¹.BlockTriangular OrderDual.toDual` using `blockTriangular_inv_of_blockTriangular hbt`. Establish `hup' : ∀ i k : Fin p, i < k → L⁻¹ i k = 0` using `fun i k h => hinv h`. Use `⟨L⁻¹, L * x, ?_, fun i => ?_, hup', fun i j h => ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]`. Establish `h` using `ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_expand L L⁻¹ i i (hup i) (hd i)`. Rewrite `h` using `[mul_nonsing_inv _ hu, Matrix.one_apply_eq, Finset.sum_eq_zero, zero_add]`. Conclude with `h.symm`. Introduce `k _`.

Rewrite using `[hup' _ i (by rw [Fin.lt_def]; exact k.isLt), mul_zero]`. Conclude with `ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_mul_up x hM i j h`.
-/
theorem exists_lowerUnitriangular_mul_upperTriangular :
    ∀ (p : ℕ) (x : Matrix (Fin p) (Fin p) ℂ), (∀ i, leadMinor x i ≠ 0) →
      ∃ n b : Matrix (Fin p) (Fin p) ℂ, x = n * b ∧ (∀ i, n i i = 1) ∧
        (∀ i j, i < j → n i j = 0) ∧ (∀ i j, j < i → b i j = 0) := by
  intro p x hx
  have hM : ∀ k : Fin (p + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor x k ≠ 0 := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      have : IsEmpty (Fin ((0 : Fin (p + 1)) : ℕ)) := inferInstanceAs (IsEmpty (Fin 0))
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
    · exact hx i
  set L := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm x with hL
  have hu : IsUnit L.det := by
    rw [hL, ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_det]; exact isUnit_one
  have hup : ∀ i k : Fin p, i < k → L i k = 0 := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_up x
  have hd : ∀ i : Fin p, L i i = 1 := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_diag x
  have hbt : L.BlockTriangular OrderDual.toDual := fun i k h => hup i k h
  let : Invertible L := L.invertibleOfIsUnitDet hu
  have hinv : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular hbt
  have hup' : ∀ i k : Fin p, i < k → L⁻¹ i k = 0 := fun i k h => hinv h
  refine ⟨L⁻¹, L * x, ?_, fun i => ?_, hup', fun i j h => ?_⟩
  · rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
  · have h := ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.row_expand L L⁻¹ i i (hup i) (hd i)
    rw [mul_nonsing_inv _ hu, Matrix.one_apply_eq, Finset.sum_eq_zero, zero_add] at h
    · exact h.symm
    · intro k _
      rw [hup' _ i (by rw [Fin.lt_def]; exact k.isLt), mul_zero]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.Lm_mul_up x hM i j h

end GlobalTheory
