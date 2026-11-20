import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `hdet hsig y hy`. Establish `hneg : ∀ i, hA.eigenvalues i < 0`. Introduce `i`. Establish `hnp : ¬ 0 < hA.eigenvalues i`. Introduce `h`.

Establish `: IsEmpty {i : Fin n // 0 < hA.eigenvalues i}` using `Fintype.card_eq_zero_iff.mp hsig`. Conclude with `this.false ⟨i, h⟩`. Establish `hne : hA.eigenvalues i ≠ 0`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises.

Rewrite using `[hA.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])`. Conclude with `lt_of_le_of_ne (not_lt.mp hnp) hne`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hUU : star U * U = 1` using `Unitary.coe_star_mul_self _`.

Establish `hUU' : U * star U = 1` using `Unitary.coe_mul_star_self _`. Use `set z : Fin n → ℂ := star U *ᵥ y with hz`. Establish `hyz : y = U *ᵥ z` using `by rw [hz, mulVec_mulVec, hUU', one_mulVec]`. Establish `hz0 : z ≠ 0`. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Rewrite using `[hyz, h, mulVec_zero]`. Establish `hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U` using `by conv_lhs => rw [hA.spectral_theorem]`. Rewrite using `[Unitary.conjStarAlgAut_apply]`. Establish `key : star y ⬝ᵥ A *ᵥ y = star z ⬝ᵥ diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ z` using `by conv_lhs => rw [hspec]`.

Rewrite using `[hz, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]`. Simplify using `only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul]`. Rewrite using `[key]`. Simplify using `only [dotProduct, mulVec_diagonal, Function.comp_apply, Complex.re_sum]`. Establish `hterm : ∀ i, (star z i * ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * z i)).re = hA.eigenvalues i * Complex.normSq (z i)`.

Introduce `i`. Rewrite using `[show (RCLike.ofReal (hA.eigenvalues i) : ℂ) = (hA.eigenvalues i : ℂ) from rfl,Pi.star_apply, mul_left_comm, Complex.re_ofReal_mul]`. Use `congr 1`. Rewrite using `[mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]`. Repeatedly rewrite using `[hterm]`.

Take `⟨j, hj⟩` from `Function.ne_iff.mp hz0`. Rewrite using `[← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin n)))]`. Use `Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hneg i).le (Complex.normSq_nonneg _)) ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos (hneg j) (Complex.normSq_pos.mpr hj)⟩` and prove the remaining obligations.
-/
theorem herm_negDef_of_sigPosH_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro hdet hsig y hy
  have hneg : ∀ i, hA.eigenvalues i < 0 := by
    intro i
    have hnp : ¬ 0 < hA.eigenvalues i := by
      intro h
      have : IsEmpty {i : Fin n // 0 < hA.eigenvalues i} := Fintype.card_eq_zero_iff.mp hsig
      exact this.false ⟨i, h⟩
    have hne : hA.eigenvalues i ≠ 0 := by
      intro h0
      apply hdet
      rw [hA.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
    exact lt_of_le_of_ne (not_lt.mp hnp) hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set z : Fin n → ℂ := star U *ᵥ y with hz
  have hyz : y = U *ᵥ z := by rw [hz, mulVec_mulVec, hUU', one_mulVec]
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [hyz, h, mulVec_zero]
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have key : star y ⬝ᵥ A *ᵥ y = star z ⬝ᵥ diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ z := by
    conv_lhs => rw [hspec]
    rw [hz, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Complex.re_sum]
  have hterm : ∀ i, (star z i * ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * z i)).re =
      hA.eigenvalues i * Complex.normSq (z i) := by
    intro i
    rw [show (RCLike.ofReal (hA.eigenvalues i) : ℂ) = (hA.eigenvalues i : ℂ) from rfl,Pi.star_apply, mul_left_comm, Complex.re_ofReal_mul]
    congr 1
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin n)))]
  refine Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hneg i).le (Complex.normSq_nonneg _))
    ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos (hneg j) (Complex.normSq_pos.mpr hj)⟩

end GlobalTheory
