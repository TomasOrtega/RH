import Mathlib

namespace Bl.general_b_fact_ter

/- English proof (translation)
Introduce `r N N' B B' hN0 hN1 hN'0 hN'1 hB0 hB'0 hdet hEq`. Establish `lN : N.BlockTriangular OrderDual.toDual` using `fun i j hij => hN0 i j (OrderDual.toDual_lt_toDual.mp hij)`. Establish `lN' : N'.BlockTriangular OrderDual.toDual` using `fun i j hij => hN'0 i j (OrderDual.toDual_lt_toDual.mp hij)`. Establish `uB : B.BlockTriangular id` using `fun i j hij => hB0 i j hij`. Establish `uB' : B'.BlockTriangular id` using `fun i j hij => hB'0 i j hij`.

Establish `dN' : N'.det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular N' lN']`. Simplify using `[hN'1]`. Establish `uN' : IsUnit N'.det` using `by rw [dN']; exact isUnit_one`. Establish `uBd : IsUnit B.det` using `isUnit_iff_ne_zero.mpr hdet`.

Establish `iN' : Invertible N'` using `Matrix.invertibleOfIsUnitDet N' uN'`. Establish `iB : Invertible B` using `Matrix.invertibleOfIsUnitDet B uBd`. Establish `hM2 : N'⁻¹ * N = B' * B⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc (N'⁻¹ * N), Matrix.mul_nonsing_inv B uBd, Matrix.mul_one]`.

Use `_ = N'⁻¹ * (N' * B') * B⁻¹ := by rw [Matrix.mul_assoc N'⁻¹ N B, hEq]`. Use `_ = B' * B⁻¹ := by`. Rewrite using `[← Matrix.mul_assoc N'⁻¹ N' B', Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]`. Take `⟨M, hM⟩ : ∃ M, M = N'⁻¹ * N` from `⟨_, rfl⟩`. Establish `lM : M.BlockTriangular OrderDual.toDual`.

Rewrite using `[hM]`. Conclude with `(Matrix.blockTriangular_inv_of_blockTriangular lN').mul lN`. Establish `uM : M.BlockTriangular id`. Rewrite using `[hM, hM2]`. Conclude with `uB'.mul (Matrix.blockTriangular_inv_of_blockTriangular uB)`.

Establish `hNM : N = N' * M`. Rewrite using `[hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]`. Establish `hoff : ∀ a c, a ≠ c → M a c = 0`. Introduce `a c hac`. Break down `lt_or_gt_of_ne hac with h | h` into its components or cases.

Conclude with `lM (OrderDual.toDual_lt_toDual.mpr h)`. Conclude with `uM h`. Establish `hdiag : ∀ a, M a a = 1`. Introduce `a`. Establish `h` using `congrFun (congrFun hNM a) a`.

Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single a (fun k _ hk => by rw [hoff k a hk, mul_zero]) (fun h => absurd (Finset.mem_univ a) h), hN'1, one_mul, hN1]`. Conclude with `h.symm`. Establish `hM1 : M = 1`. Use extensionality with `a c`. Distinguish the cases in `h : a = c`.

Substitute `h` using the available equality. Rewrite using `[hdiag, Matrix.one_apply_eq]`. Rewrite using `[hoff a c h, Matrix.one_apply_ne h]`. Rewrite using `[hNM, hM1, Matrix.mul_one]`.
-/
theorem goal1 :
  ∀ {r : Nat} {N N' B B' : Matrix.{0, 0, 0} (Fin r) (Fin r) Complex},
  (∀ (a c : Fin r), LT.lt.{0} a c → Eq.{1} (N a c) 0) →
    (∀ (a : Fin r), Eq.{1} (N a a) 1) →
      (∀ (a c : Fin r), LT.lt.{0} a c → Eq.{1} (N' a c) 0) →
        (∀ (a : Fin r), Eq.{1} (N' a a) 1) →
          (∀ (a c : Fin r), LT.lt.{0} c a → Eq.{1} (B a c) 0) →
            (∀ (a c : Fin r), LT.lt.{0} c a → Eq.{1} (B' a c) 0) →
              Ne.{1} (Matrix.det.{0, 0} B) 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N B) (HMul.hMul.{0, 0, 0} N' B') → Eq.{1} N N'  := by
  intro r N N' B B' hN0 hN1 hN'0 hN'1 hB0 hB'0 hdet hEq
  have lN : N.BlockTriangular OrderDual.toDual := fun i j hij =>
    hN0 i j (OrderDual.toDual_lt_toDual.mp hij)
  have lN' : N'.BlockTriangular OrderDual.toDual := fun i j hij =>
    hN'0 i j (OrderDual.toDual_lt_toDual.mp hij)
  have uB : B.BlockTriangular id := fun i j hij => hB0 i j hij
  have uB' : B'.BlockTriangular id := fun i j hij => hB'0 i j hij
  have dN' : N'.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N' lN']
    simp [hN'1]
  have uN' : IsUnit N'.det := by rw [dN']; exact isUnit_one
  have uBd : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have iN' : Invertible N' := Matrix.invertibleOfIsUnitDet N' uN'
  have iB : Invertible B := Matrix.invertibleOfIsUnitDet B uBd
  have hM2 : N'⁻¹ * N = B' * B⁻¹ := by
    calc N'⁻¹ * N = N'⁻¹ * N * B * B⁻¹ := by
          rw [Matrix.mul_assoc (N'⁻¹ * N), Matrix.mul_nonsing_inv B uBd, Matrix.mul_one]
      _ = N'⁻¹ * (N' * B') * B⁻¹ := by rw [Matrix.mul_assoc N'⁻¹ N B, hEq]
      _ = B' * B⁻¹ := by
          rw [← Matrix.mul_assoc N'⁻¹ N' B', Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]
  obtain ⟨M, hM⟩ : ∃ M, M = N'⁻¹ * N := ⟨_, rfl⟩
  have lM : M.BlockTriangular OrderDual.toDual := by
    rw [hM]; exact (Matrix.blockTriangular_inv_of_blockTriangular lN').mul lN
  have uM : M.BlockTriangular id := by
    rw [hM, hM2]; exact uB'.mul (Matrix.blockTriangular_inv_of_blockTriangular uB)
  have hNM : N = N' * M := by
    rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]
  have hoff : ∀ a c, a ≠ c → M a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact lM (OrderDual.toDual_lt_toDual.mpr h)
    · exact uM h
  have hdiag : ∀ a, M a a = 1 := by
    intro a
    have h := congrFun (congrFun hNM a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a (fun k _ hk => by rw [hoff k a hk, mul_zero])
      (fun h => absurd (Finset.mem_univ a) h), hN'1, one_mul, hN1] at h
    exact h.symm
  have hM1 : M = 1 := by
    ext a c
    by_cases h : a = c
    · subst h; rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff a c h, Matrix.one_apply_ne h]
  rw [hNM, hM1, Matrix.mul_one]

end Bl.general_b_fact_ter
