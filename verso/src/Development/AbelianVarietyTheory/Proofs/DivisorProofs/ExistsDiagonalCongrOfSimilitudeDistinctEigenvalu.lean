import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `n h g c Z lam hh hdet hc hg hinj hnorm hgZ`. Use `set M : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hM`. Use `set H : Matrix (Fin n) (Fin n) ℂ := Mᴴ * h * M with hH`. Establish `hHherm : H.IsHermitian`. Simplify using `only [hH, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hh.eq, Matrix.mul_assoc]`.

Establish `key : (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam = (c : ℂ) • H`. Establish `e1 : (M * Matrix.diagonal lam)ᴴ * h * (M * Matrix.diagonal lam) = (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam`. Simplify using `only [hH, conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← e1, ← hgZ]`. Simplify using `only [hH, conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc (gᴴ * h), hg]`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`. Establish `hc' : ∀ i, (starRingEnd ℂ) (lam i) * lam i = (c : ℂ)`. Introduce `i`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Conclude with `hnorm i` after adjusting the coercions. Establish `hlam0 : ∀ i, lam i ≠ 0`. Introduce `i h0`. Use `hnorm i` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `hc (by simpa using this.symm)`. Establish `hoff : ∀ i j, i ≠ j → H i j = 0`. Introduce `i j hij`. Establish `e` using `congrFun (congrFun key i) j`. Rewrite `e` using `[Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul]`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul] at e`. Establish `hne : lam j - lam i ≠ 0` using `sub_ne_zero.mpr (fun h => hij (hinj h).symm)`. Establish `hstar : (starRingEnd ℂ) (lam i) ≠ 0` using `by simpa using hlam0 i`. Establish `e2 : (starRingEnd ℂ) (lam i) * (lam j - lam i) * H i j = 0`. Rewrite `e` using `[← hc' i]`.

Simplify using `only [Pi.star_apply] at e`. Establish `: star (lam i) = (starRingEnd ℂ) (lam i)` using `rfl`. Rewrite `e` using `[this]`. Take the linear combination `e`. Break down `mul_eq_zero.mp e2 with h1 | h1` into its components or cases.

Conclude with `absurd h1 (mul_ne_zero hstar hne)`. Conclude with `h1`. Establish `hdiag : H = Matrix.diagonal (fun i => (((H i i).re : ℝ) : ℂ))`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq]`. Conclude with `(hHherm.coe_re_apply_self i).symm`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, hoff i j hij]`. Use `⟨fun i => (H i i).re, ?_, hdiag⟩` and prove the remaining obligations.

Establish `hdetH : H.det ≠ 0`. Establish `hMdet : M.det ≠ 0`. Rewrite using `[hM]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit |>.ne_zero`. Simplify using `only [hH, Matrix.det_mul, Matrix.det_conjTranspose]`.

Conclude with `mul_ne_zero (mul_ne_zero (by simpa using hMdet) hdet) hMdet`. Introduce `i hi`. Rewrite `hdetH` using `[hdiag, Matrix.det_diagonal]`. Apply `hdetH` to reduce the goal to its premises. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])`.
-/
theorem similitude_eigvec_orthogonal : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  intro n h g c Z lam hh hdet hc hg hinj hnorm hgZ
  set M : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  set H : Matrix (Fin n) (Fin n) ℂ := Mᴴ * h * M with hH
  have hHherm : H.IsHermitian := by
    simp only [hH, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hh.eq, Matrix.mul_assoc]
  have key : (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam = (c : ℂ) • H := by
    have e1 : (M * Matrix.diagonal lam)ᴴ * h * (M * Matrix.diagonal lam) = (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam := by
      simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← e1, ← hgZ]
    simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc (gᴴ * h), hg]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hc' : ∀ i, (starRingEnd ℂ) (lam i) * lam i = (c : ℂ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast hnorm i
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i h0
    have := hnorm i
    rw [h0, norm_zero] at this
    exact hc (by simpa using this.symm)
  have hoff : ∀ i j, i ≠ j → H i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun key i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul] at e
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h).symm)
    have hstar : (starRingEnd ℂ) (lam i) ≠ 0 := by simpa using hlam0 i
    have e2 : (starRingEnd ℂ) (lam i) * (lam j - lam i) * H i j = 0 := by
      rw [← hc' i] at e
      simp only [Pi.star_apply] at e
      have : star (lam i) = (starRingEnd ℂ) (lam i) := rfl
      rw [this] at e
      linear_combination e
    rcases mul_eq_zero.mp e2 with h1 | h1
    · exact absurd h1 (mul_ne_zero hstar hne)
    · exact h1
  have hdiag : H = Matrix.diagonal (fun i => (((H i i).re : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact (hHherm.coe_re_apply_self i).symm
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun i => (H i i).re, ?_, hdiag⟩
  have hdetH : H.det ≠ 0 := by
    have hMdet : M.det ≠ 0 := by
      rw [hM]; exact (Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit |>.ne_zero
    simp only [hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (by simpa using hMdet) hdet) hMdet
  intro i hi
  rw [hdiag, Matrix.det_diagonal] at hdetH
  apply hdetH
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end GlobalTheory
