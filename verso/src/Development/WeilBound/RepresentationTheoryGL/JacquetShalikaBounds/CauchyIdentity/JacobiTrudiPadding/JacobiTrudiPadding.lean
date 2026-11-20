import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

open Finset Matrix

namespace PositivityTheory.RgJS

namespace JacobiTrudiPadding

/- English proof (translation)
Simplify using `[hZ, hN, Finset.Nat.antidiagonalTuple_zero_right]`.
-/
theorem hZ_zero {m : ℕ} (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp [hZ, hN, Finset.Nat.antidiagonalTuple_zero_right]

/- English proof (translation)
Simplify using `[hZ, hz]`.
-/
theorem hZ_neg {m : ℕ} (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular]`. Simplify using `[hZ_zero]`. Introduce `i j hij`. Simplify using `only [Matrix.of_apply]`. Apply `hZ_neg` to reduce the goal to its premises.

Establish `: (i : ℕ) < j` using `hij`. Use linear arithmetic over natural numbers and integers.
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
Unfold `jt`. Rewrite using `[← Matrix.det_submatrix_equiv_self finSumFinEquiv]`. Rewrite using `[← Matrix.fromBlocks_toBlocks (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv)]`. Rewrite using `[show Matrix.toBlocks₁₂ (Matrix.submatrix _ finSumFinEquiv finSumFinEquiv) = 0 from ?_]`. Rewrite using `[Matrix.det_fromBlocks_zero₁₂]`.

Establish `h11 : Matrix.toBlocks₁₁ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin m') => hZ (↑(l j) - ↑↑j + ↑↑i) α`. Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₁₁, padN]`. Establish `h22 : Matrix.toBlocks₂₂ ((of fun (i j : Fin (m' + d)) => hZ (↑(padN (m' + d) l j) - ↑↑j + ↑↑i) α).submatrix finSumFinEquiv finSumFinEquiv) = of fun (i j : Fin d) => hZ ((i : ℤ) - j) α`. Use extensionality with `i j`.

Simplify using `[Matrix.toBlocks₂₂, padN]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h11, h22, det_unitri, mul_one]`. Use extensionality with `i j`.

Simplify using `[Matrix.toBlocks₁₂, padN]`. Apply `hZ_neg` to reduce the goal to its premises. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
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
Introduce `m m' hm α l`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Conclude with `JacobiTrudiPadding.jt_pad_add m' d α l`.
-/
theorem jacobi_trudi_padding : JTPad := by
  intro m m' hm α l
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact JacobiTrudiPadding.jt_pad_add m' d α l

end PositivityTheory.RgJS
