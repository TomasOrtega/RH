import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

open Finset Matrix

namespace PositivityTheory.RgJS

namespace JacobiTrudiPadding

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hZ_zero {m : ℕ} (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp [hZ, hN, Finset.Nat.antidiagonalTuple_zero_right]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hZ_neg {m : ℕ} (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem det_unitri {m d : ℕ} (α : Fin m → ℂ) : (Matrix.of fun i j : Fin d => hZ ((i : ℤ) - j) α).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hZ_zero]
  · intro i j hij
    simp only [Matrix.of_apply]
    apply hZ_neg
    have : (i : ℕ) < j := hij
    omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem jt_pad_add (m' d : ℕ) (α : Fin (m' + d) → ℂ) (l : Fin m' → ℕ) :
    jt α (padN (m' + d) l) = jt α l := by
  unfold jt
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  rw [← Matrix.fromBlocks_toBlocks (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv)]
  rw [show Matrix.toBlocks₁₂ (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv) = 0 from ?_]
  · rw [Matrix.det_fromBlocks_zero₁₂]
    have h11 : Matrix.toBlocks₁₁ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix
        finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin m') => hZ (↑(l j) - ↑↑j + ↑↑i) α := by
      ext i j
      simp [Matrix.toBlocks₁₁, padN]
    have h22 : Matrix.toBlocks₂₂ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix
        finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin d) => hZ ((i : ℤ) - j) α := by
      ext i j
      simp [Matrix.toBlocks₂₂, padN]
      congr 1
      ring
    rw [h11, h22, det_unitri, mul_one]
  · ext i j
    simp [Matrix.toBlocks₁₂, padN]
    apply hZ_neg
    have := i.isLt
    omega

end JacobiTrudiPadding

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem jacobi_trudi_padding : JTPad := by
  intro m m' hm α l
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact JacobiTrudiPadding.jt_pad_add m' d α l

end PositivityTheory.RgJS
