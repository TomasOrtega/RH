import Mathlib

namespace Bl.general_b_fact_variant

/- English proof (translation)
Introduce `n N N' B B' h1 h2 h3 h4 h5 h6 h7 h8`. Establish `hN' : N'.det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular N' h2]`. Simplify using `[h4]`. Establish `hu : IsUnit N'.det` using `by rw [hN']; exact isUnit_one`.

Establish `hB : IsUnit B.det` using `isUnit_iff_ne_zero.mpr h7`. Set `_iN : Invertible N'` to `Matrix.invertibleOfIsUnitDet N' hu`. Set `_iB : Invertible B` to `Matrix.invertibleOfIsUnitDet B hB`. Use `set M := N'⁻¹ * N with hM`. Establish `hMl : M.BlockTriangular OrderDual.toDual` using `(Matrix.blockTriangular_inv_of_blockTriangular h2).mul h1`.

Establish `hMe : M = B' * B⁻¹`. Rewrite using `[hM, ← Matrix.mul_one (N'⁻¹ * N), ← Matrix.mul_nonsing_inv B hB, ← Matrix.mul_assoc, Matrix.mul_assoc N'⁻¹ N B, h8, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul N' hu, Matrix.one_mul]`. Establish `hMu : M.BlockTriangular id`. Rewrite using `[hMe]`. Conclude with `h6.mul (Matrix.blockTriangular_inv_of_blockTriangular h5)`.

Establish `hoff : ∀ i j, i ≠ j → M i j = 0`. Introduce `i j hij`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `hMl h`. Conclude with `hMu h`.

Establish `hNM : N = N' * M`. Rewrite using `[hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' hu, Matrix.one_mul]`. Establish `hdiag : ∀ i, M i i = 1`. Introduce `i`. Use `congrFun (congrFun hNM i) i` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `this` using `[h3, h4, one_mul]`. Conclude with `this.symm`. Introduce `k _ hk`. Rewrite using `[hoff k i hk, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `hM1 : M = 1`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[hdiag, Matrix.one_apply_eq]`. Rewrite using `[hoff i j hij, Matrix.one_apply_ne hij]`. Rewrite using `[hNM, hM1, Matrix.mul_one]`.
-/
theorem goal1 :
  ∀ {n : Nat} {N N' B B' : Matrix.{0, 0, 0} (Fin n) (Fin n) Complex},
  Matrix.BlockTriangular.{0, 0, 0} N (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
    Matrix.BlockTriangular.{0, 0, 0} N' (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
      (∀ (i : Fin n), Eq.{1} (N i i) 1) →
        (∀ (i : Fin n), Eq.{1} (N' i i) 1) →
          Matrix.BlockTriangular.{0, 0, 0} B id.{1} →
            Matrix.BlockTriangular.{0, 0, 0} B' id.{1} →
              Ne.{1} (Matrix.det.{0, 0} B) 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N B) (HMul.hMul.{0, 0, 0} N' B') → Eq.{1} N N' := by
  intro n N N' B B' h1 h2 h3 h4 h5 h6 h7 h8
  classical
  have hN' : N'.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N' h2]
    simp [h4]
  have hu : IsUnit N'.det := by rw [hN']; exact isUnit_one
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr h7
  let _iN : Invertible N' := Matrix.invertibleOfIsUnitDet N' hu
  let _iB : Invertible B := Matrix.invertibleOfIsUnitDet B hB
  set M := N'⁻¹ * N with hM
  have hMl : M.BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular h2).mul h1
  have hMe : M = B' * B⁻¹ := by
    rw [hM, ← Matrix.mul_one (N'⁻¹ * N), ← Matrix.mul_nonsing_inv B hB, ← Matrix.mul_assoc,
      Matrix.mul_assoc N'⁻¹ N B, h8, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul N' hu, Matrix.one_mul]
  have hMu : M.BlockTriangular id := by
    rw [hMe]
    exact h6.mul (Matrix.blockTriangular_inv_of_blockTriangular h5)
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hMl h
    · exact hMu h
  have hNM : N = N' * M := by
    rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' hu, Matrix.one_mul]
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    have := congrFun (congrFun hNM i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at this
    · rw [h3, h4, one_mul] at this
      exact this.symm
    · intro k _ hk
      rw [hoff k i hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hM1 : M = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff i j hij, Matrix.one_apply_ne hij]
  rw [hNM, hM1, Matrix.mul_one]

end Bl.general_b_fact_variant
