import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DetMonotone

/- English proof (translation)
Use `⟨(hA.eigenvectorUnitary : Matrix κ κ ℂ), Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hA.spectral_theorem]`. Both sides reduce to the same expression.
-/
private theorem exists_unitary_diagonal_eigenvalues_of_isHermitian {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
  refine ⟨(hA.eigenvectorUnitary : Matrix κ κ ℂ), Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rfl

/- English proof (translation)
Use `open ComplexOrder in (`. Establish `one_le_re_det_lemma_2 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ}, Q.PosSemidef → 1 ≤ ((1 + Q).det).re`. Introduce `κ _ _ Q hQ`. Take `⟨U, h1, h2, hU⟩` from `exists_unitary_diagonal_eigenvalues_of_isHermitian hQ.1`. Establish `hsum : 1 + Q = U * diagonal (fun i => 1 + (hQ.1.eigenvalues i : ℂ)) * star U` using `by conv_lhs => rw [hU]`.

Rewrite using `[← diagonal_add, diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]`. Establish `hdet : (1 + Q).det = ∏ i, (1 + (hQ.1.eigenvalues i : ℂ))`. Rewrite using `[hsum, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, h2, det_one, one_mul]`. Rewrite using `[hdet, show (∏ i, (1 + (hQ.1.eigenvalues i : ℂ))) = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]`. Combine the equalities or inequalities in the displayed calculation.

Introduce `κ _ _ X Y hX hP`. Establish `hY : Y = X + (Y - X)` using `by abel`. Distinguish the cases in `h0 : X.det = 0`. Rewrite using `[h0, Complex.zero_re]`. Establish `hnn` using `(hX.add hP).det_nonneg`.

Rewrite `hnn` using `[← hY]`. Conclude with `(Complex.le_def.1 hnn).1`. Take `⟨U, h1, h2, hU⟩` from `exists_unitary_diagonal_eigenvalues_of_isHermitian hX.1`. Establish `hpos : ∀ i, 0 < hX.1.eigenvalues i`. Introduce `i`.

Use `lt_of_le_of_ne (hX.eigenvalues_nonneg i) fun h => h0 ?_` and prove the remaining obligations. Rewrite using `[hX.1.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h]; simp)`. Use `set s : κ → ℂ := fun i => ((Real.sqrt (hX.1.eigenvalues i) : ℝ) : ℂ) with hs`. Establish `hs0 : ∀ i, s i ≠ 0` using `fun i => by`.

Simplify using `only [hs, ne_eq, Complex.ofReal_eq_zero]`. Conclude with `(Real.sqrt_pos.2 (hpos i)).ne'`. Establish `hss : ∀ i, s i * s i = (hX.1.eigenvalues i : ℂ)` using `fun i => by`. Simplify using `only [hs]`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]`.

Establish `hstar : ∀ i, star (s i) = s i` using `fun i => by simp [hs]`. Use `set B : Matrix κ κ ℂ := diagonal s * star U with hB`. Use `set C : Matrix κ κ ℂ := U * diagonal (fun i => (s i)⁻¹) with hC`. Establish `hCB : C * B = 1`. Rewrite using `[hB, hC, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal, show (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hs0 i), diagonal_one, Matrix.one_mul, h1]`.

Establish `hXB : X = Bᴴ * B`. Rewrite using `[hB, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose, show star s = s from funext hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), diagonal_mul_diagonal, show (fun i => s i * s i) = fun i => (hX.1.eigenvalues i : ℂ) from fune …`. Conclude with `hU`. Establish `hsplit : Y = Bᴴ * (1 + Cᴴ * (Y - X) * C) * B`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hXB, Matrix.mul_assoc, Matrix.mul_assoc, hCB, Matrix.mul_one, ← Matrix.mul_assoc, ← conjTranspose_mul, hCB, conjTranspose_one, Matrix.one_mul]`.

Normalize the expressions using the abelian group laws. Establish `hQ : (Cᴴ * (Y - X) * C).PosSemidef` using `hP.conjTranspose_mul_mul_same C`. Establish `hdX : X.det = Bᴴ.det * B.det` using `by rw [hXB, det_mul]`. Use `clear_value B C`. Establish `hdY : Y.det = (1 + Cᴴ * (Y - X) * C).det * X.det` using `by conv_lhs => rw [hsplit]`.

Rewrite using `[det_mul, det_mul, hdX]`. Expand and normalize the polynomial expressions, which then agree. Establish `hXnn` using `Complex.le_def.1 hX.det_nonneg`. Establish `hQnn` using `Complex.le_def.1 (PosSemidef.one.add hQ).det_nonneg`. Rewrite using `[hdY, Complex.mul_re, ← hXnn.2, ← hQnn.2]`.

Simplify using `only [Complex.zero_im, mul_zero, sub_zero]`. Establish `ha : 0 ≤ X.det.re` using `by simpa using hXnn.1`. Conclude with `le_mul_of_one_le_left ha (one_le_re_det_lemma_2 hQ))`.
-/
theorem detMono : DetMono := by
  open ComplexOrder in (
    have one_le_re_det_lemma_2 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ},
        Q.PosSemidef → 1 ≤ ((1 + Q).det).re := by
      intro κ _ _ Q hQ
      obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hQ.1
      have hsum : 1 + Q = U * diagonal (fun i => 1 + (hQ.1.eigenvalues i : ℂ)) * star U := by
        conv_lhs => rw [hU]
        rw [← diagonal_add, diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
      have hdet : (1 + Q).det = ∏ i, (1 + (hQ.1.eigenvalues i : ℂ)) := by
        rw [hsum, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, h2, det_one, one_mul]
      rw [hdet, show (∏ i, (1 + (hQ.1.eigenvalues i : ℂ))) = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re]
      calc (1 : ℝ) = ∏ _i : κ, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => le_add_of_nonneg_right (hQ.eigenvalues_nonneg i)
    intro κ _ _ X Y hX hP
    have hY : Y = X + (Y - X) := by abel
    by_cases h0 : X.det = 0
    · rw [h0, Complex.zero_re]
      have hnn := (hX.add hP).det_nonneg
      rw [← hY] at hnn
      exact (Complex.le_def.1 hnn).1
    · obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hX.1
      have hpos : ∀ i, 0 < hX.1.eigenvalues i := by
        intro i
        refine lt_of_le_of_ne (hX.eigenvalues_nonneg i) fun h => h0 ?_
        rw [hX.1.det_eq_prod_eigenvalues]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h]; simp)
      set s : κ → ℂ := fun i => ((Real.sqrt (hX.1.eigenvalues i) : ℝ) : ℂ) with hs
      have hs0 : ∀ i, s i ≠ 0 := fun i => by
        simp only [hs, ne_eq, Complex.ofReal_eq_zero]
        exact (Real.sqrt_pos.2 (hpos i)).ne'
      have hss : ∀ i, s i * s i = (hX.1.eigenvalues i : ℂ) := fun i => by
        simp only [hs]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
      have hstar : ∀ i, star (s i) = s i := fun i => by simp [hs]
      set B : Matrix κ κ ℂ := diagonal s * star U with hB
      set C : Matrix κ κ ℂ := U * diagonal (fun i => (s i)⁻¹) with hC
      have hCB : C * B = 1 := by
        rw [hB, hC, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
          show (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hs0 i),
          diagonal_one, Matrix.one_mul, h1]
      have hXB : X = Bᴴ * B := by
        rw [hB, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose,
          show star s = s from funext hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
          diagonal_mul_diagonal, show (fun i => s i * s i) = fun i => (hX.1.eigenvalues i : ℂ) from funext hss,
          ← Matrix.mul_assoc, ← star_eq_conjTranspose]
        exact hU
      have hsplit : Y = Bᴴ * (1 + Cᴴ * (Y - X) * C) * B := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hXB, Matrix.mul_assoc, Matrix.mul_assoc, hCB,
          Matrix.mul_one, ← Matrix.mul_assoc, ← conjTranspose_mul, hCB, conjTranspose_one, Matrix.one_mul]
        abel
      have hQ : (Cᴴ * (Y - X) * C).PosSemidef := hP.conjTranspose_mul_mul_same C
      have hdX : X.det = Bᴴ.det * B.det := by rw [hXB, det_mul]
      clear_value B C
      have hdY : Y.det = (1 + Cᴴ * (Y - X) * C).det * X.det := by
        conv_lhs => rw [hsplit]
        rw [det_mul, det_mul, hdX]
        ring
      have hXnn := Complex.le_def.1 hX.det_nonneg
      have hQnn := Complex.le_def.1 (PosSemidef.one.add hQ).det_nonneg
      rw [hdY, Complex.mul_re, ← hXnn.2, ← hQnn.2]
      simp only [Complex.zero_im, mul_zero, sub_zero]
      have ha : 0 ≤ X.det.re := by simpa using hXnn.1
      exact le_mul_of_one_le_left ha (one_le_re_det_lemma_2 hQ))

end GlobalTheory.CompanionTheory.DetMonotone
