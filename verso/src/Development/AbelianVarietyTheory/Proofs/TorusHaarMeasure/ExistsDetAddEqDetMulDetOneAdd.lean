import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

open scoped MatrixOrder in

/- English proof (translation)
Establish `hP0 : (0 : Matrix n n ℂ) ≤ P` using `nonneg_iff_posSemidef.mpr hP`. Use `set S := CFC.sqrt P with hSdef`. Establish `hS0 : (0 : Matrix n n ℂ) ≤ S` using `CFC.sqrt_nonneg P`. Establish `hSS : S * S = P` using `CFC.sqrt_mul_sqrt_self P hP0`. Establish `hSh : Sᴴ = S` using `(nonneg_iff_posSemidef.mp hS0).1`.

Establish `hdS : S.det ≠ 0`. Introduce `h`. Apply `hd` to reduce the goal to its premises. Rewrite using `[← hSS, det_mul, h, zero_mul]`. Establish `hSu : IsUnit S.det` using `isUnit_iff_ne_zero.mpr hdS`.

Establish `hl : S * S⁻¹ = 1` using `mul_nonsing_inv S hSu`. Establish `hr : S⁻¹ * S = 1` using `nonsing_inv_mul S hSu`. Establish `hback : S * (S⁻¹ * Q * S⁻¹) * S = Q`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Q := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]`. Use `⟨S⁻¹ * Q * S⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hQ.conjTranspose_mul_mul_same S⁻¹`. Rewrite `h` using `[conjTranspose_nonsing_inv, hSh]`. Then use the resulting hypothesis. Introduce `h`.

Rewrite using `[← hback, h, Matrix.mul_zero, Matrix.zero_mul]`. Establish `hPQ : P + Q = S * (1 + S⁻¹ * Q * S⁻¹) * S`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, hback]`. Rewrite using `[hPQ, det_mul, det_mul, ← hSS, det_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_det_add_eq_det_mul_det_one_add {n : Type} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hd : P.det ≠ 0) :
    ∃ R : Matrix n n ℂ, R.PosSemidef ∧ (R = 0 → Q = 0) ∧ (P + Q).det = P.det * (1 + R).det := by
  have hP0 : (0 : Matrix n n ℂ) ≤ P := nonneg_iff_posSemidef.mpr hP
  set S := CFC.sqrt P with hSdef
  have hS0 : (0 : Matrix n n ℂ) ≤ S := CFC.sqrt_nonneg P
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP0
  have hSh : Sᴴ = S := (nonneg_iff_posSemidef.mp hS0).1
  have hdS : S.det ≠ 0 := by
    intro h
    apply hd
    rw [← hSS, det_mul, h, zero_mul]
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hdS
  have hl : S * S⁻¹ = 1 := mul_nonsing_inv S hSu
  have hr : S⁻¹ * S = 1 := nonsing_inv_mul S hSu
  have hback : S * (S⁻¹ * Q * S⁻¹) * S = Q := by
    calc S * (S⁻¹ * Q * S⁻¹) * S = (S * S⁻¹) * Q * (S⁻¹ * S) := by
          simp only [Matrix.mul_assoc]
      _ = Q := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]
  refine ⟨S⁻¹ * Q * S⁻¹, ?_, ?_, ?_⟩
  · have h := hQ.conjTranspose_mul_mul_same S⁻¹
    rwa [conjTranspose_nonsing_inv, hSh] at h
  · intro h
    rw [← hback, h, Matrix.mul_zero, Matrix.zero_mul]
  · have hPQ : P + Q = S * (1 + S⁻¹ * Q * S⁻¹) * S := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, hback]
    rw [hPQ, det_mul, det_mul, ← hSS, det_mul]
    ring

/- English proof (translation)
Use `set U : Matrix n n ℂ := (hR.1.eigenvectorUnitary : Matrix n n ℂ) with hU`. Establish `hspec : R = U * diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) * star U` using `by conv_lhs => rw [hR.1.spectral_theorem]`. Both sides reduce to the same expression. Establish `hUU : U * star U = 1` using `Unitary.mul_star_self_of_mem hR.1.eigenvectorUnitary.2`. Establish `hdU : U.det * (star U).det = 1` using `by rw [← det_mul, hUU, det_one]`.

Establish `h1 : 1 + R = U * diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) * star U`. Establish `hd1 : diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) = 1 + diagonal (RCLike.ofReal ∘ hR.1.eigenvalues)`. Rewrite using `[← diagonal_one, diagonal_add]`. Both sides reduce to the same expression. Rewrite using `[hd1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hspec]`.

Rewrite using `[h1, det_mul, det_mul, det_diagonal, mul_right_comm, hdU, one_mul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private lemma det_one_add_eq_prod_eigenvalues {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℂ}
    (hR : R.PosSemidef) :
    (1 + R).det = ((∏ i, (1 + hR.1.eigenvalues i) : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hR.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hspec : R = U * diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) * star U := by
    conv_lhs => rw [hR.1.spectral_theorem]
    rfl
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hR.1.eigenvectorUnitary.2
  have hdU : U.det * (star U).det = 1 := by rw [← det_mul, hUU, det_one]
  have h1 : 1 + R = U * diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) * star U := by
    have hd1 : diagonal (fun i => 1 + (hR.1.eigenvalues i : ℂ)) =
        1 + diagonal (RCLike.ofReal ∘ hR.1.eigenvalues) := by
      rw [← diagonal_one, diagonal_add]
      rfl
    rw [hd1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hspec]
  rw [h1, det_mul, det_mul, det_diagonal, mul_right_comm, hdU, one_mul]
  push_cast
  rfl

/- English proof (translation)
Use `⟨∏ i, (1 + hR.1.eigenvalues i), det_one_add_eq_prod_eigenvalues hR, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i)`. Introduce `hc`. Apply `hR.1.eigenvalues_eq_zero_iff.mp` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Establish `hj : 1 + hR.1.eigenvalues j ≤ ∏ i, (1 + hR.1.eigenvalues i)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]`. Conclude with `le_mul_of_one_le_right (by linarith [hR.eigenvalues_nonneg j]) (Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i))`. Use `hR.eigenvalues_nonneg j` as an intermediate fact. Simplify using `only [Pi.zero_apply]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma exists_one_le_det_one_add_of_posSemidef {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℂ}
    (hR : R.PosSemidef) :
    ∃ c : ℝ, (1 + R).det = c ∧ 1 ≤ c ∧ (c ≤ 1 → R = 0) := by
  refine ⟨∏ i, (1 + hR.1.eigenvalues i), det_one_add_eq_prod_eigenvalues hR, ?_, ?_⟩
  · exact Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i)
  · intro hc
    apply hR.1.eigenvalues_eq_zero_iff.mp
    funext j
    have hj : 1 + hR.1.eigenvalues j ≤ ∏ i, (1 + hR.1.eigenvalues i) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
      exact le_mul_of_one_le_right (by linarith [hR.eigenvalues_nonneg j])
        (Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hR.eigenvalues_nonneg i))
    have := hR.eigenvalues_nonneg j
    simp only [Pi.zero_apply]
    linarith

/- English proof (translation)
Introduce `n _ _ P Q hP hQ`. Take `⟨hPre, hPim⟩` from `Complex.nonneg_iff.mp hP.det_nonneg`. Take `⟨hSre, -⟩` from `Complex.nonneg_iff.mp (hP.add hQ).det_nonneg`. Distinguish the cases in `hd : P.det = 0`. Use `⟨hPre, ?_, fun h => absurd hd h⟩` and prove the remaining obligations.

Rewrite using `[hd, Complex.zero_re]`. Conclude with `hSre`. Take `⟨R, hR, hR0, hdet⟩` from `exists_det_add_eq_det_mul_det_one_add hP hQ hd`. Take `⟨c, hc, hc1, hcR⟩` from `exists_one_le_det_one_add_of_posSemidef hR`. Establish `hre : (P + Q).det.re = P.det.re * c`.

Rewrite using `[hdet, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]`. Establish `hpos : 0 < P.det.re`. Break down `hPre.lt_or_eq with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (Complex.ext (by rw [← h, Complex.zero_re]) (by rw [← hPim, Complex.zero_im])) hd`.

Use `⟨hPre, ?_, fun _ hle => hR0 (hcR ?_)⟩` and prove the remaining obligations. Rewrite using `[hre]`. Conclude with `le_mul_of_one_le_right hPre hc1`. Rewrite `hle` using `[hre]`. Assume the negation of the conclusion as `hlt`.

Establish `: P.det.re * 1 < P.det.re * c` using `mul_lt_mul_of_pos_left (not_le.mp hlt) hpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem det_re_mono_of_posSemidef :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef →
      0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧
        (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0) := by
  intro n _ _ P Q hP hQ
  obtain ⟨hPre, hPim⟩ := Complex.nonneg_iff.mp hP.det_nonneg
  obtain ⟨hSre, -⟩ := Complex.nonneg_iff.mp (hP.add hQ).det_nonneg
  by_cases hd : P.det = 0
  · refine ⟨hPre, ?_, fun h => absurd hd h⟩
    rw [hd, Complex.zero_re]
    exact hSre
  · obtain ⟨R, hR, hR0, hdet⟩ := exists_det_add_eq_det_mul_det_one_add hP hQ hd
    obtain ⟨c, hc, hc1, hcR⟩ := exists_one_le_det_one_add_of_posSemidef hR
    have hre : (P + Q).det.re = P.det.re * c := by
      rw [hdet, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hpos : 0 < P.det.re := by
      rcases hPre.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by rw [← h, Complex.zero_re]) (by rw [← hPim, Complex.zero_im])) hd
    refine ⟨hPre, ?_, fun _ hle => hR0 (hcR ?_)⟩
    · rw [hre]
      exact le_mul_of_one_le_right hPre hc1
    · rw [hre] at hle
      by_contra hlt
      have : P.det.re * 1 < P.det.re * c := mul_lt_mul_of_pos_left (not_le.mp hlt) hpos
      linarith

end GlobalTheory
