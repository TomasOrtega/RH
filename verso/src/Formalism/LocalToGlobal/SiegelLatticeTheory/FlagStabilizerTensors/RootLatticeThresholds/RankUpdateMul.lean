import Mathlib

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

def Ymat (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J

/- English proof (translation)
Establish `hinv : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1` using `Matrix.nonsing_inv_mul _ hΓ`. Unfold `Ymat`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]`. Use `_ = W * (1 + M) := by rw [hinv, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]`.
-/
theorem rankUpdate_mul (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (hΓ : IsUnit (Wᴴ * J * W).det) :
    Ymat J W M * W = W * (1 + M) := by
  have hinv : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  unfold Ymat
  calc (1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J) * W
        = W + W * M * ((Wᴴ * J * W)⁻¹ * (Wᴴ * J * W)) := by
          simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = W * (1 + M) := by rw [hinv, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]

/- English proof (translation)
Unfold `Ymat`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem Ymat_sub (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by
  unfold Ymat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Establish `hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]`. Establish `hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1` using `Matrix.nonsing_inv_mul _ hΓ`. Establish `hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hΓ`. Establish `hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hGh]`.

Unfold `Ymat`. Use `set G := Wᴴ * J * W with hG`. Use `set Gi := G⁻¹ with hGi`. Establish `hK : G * M + Mᴴ * G + Mᴴ * G * M = 0`. Establish `h'` using `hM`.

Rewrite `h'` using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one]`. Establish `e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M)` using `by noncomm_ring`. Rewrite `h'` using `[e]`. Conclude with `add_eq_left.1 h'`. Establish `hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hGi1, hGi2]`. Use `noncomm_ring`. Use `_ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring`. Use `_ = 0 := by rw [hK]; noncomm_ring`.

Establish `key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0`. Rewrite using `[hbr]`. Simplify using the standard rewrite rules. Simplify using `only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, hGih]`. Use `Eq.trans ?_ (add_zero J)` and prove the remaining obligations.

Rewrite using `[← key]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]`. Normalize the expressions using the abelian group laws.
-/
theorem Ymat_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ)
    (hΓ : IsUnit (Wᴴ * J * W).det) (hM : (1 + M)ᴴ * (Wᴴ * J * W) * (1 + M) = Wᴴ * J * W) :
    (Ymat J W M)ᴴ * J * Ymat J W M = J := by
  have hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  have hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΓ
  have hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  unfold Ymat
  set G := Wᴴ * J * W with hG
  set Gi := G⁻¹ with hGi

  have hK : G * M + Mᴴ * G + Mᴴ * G * M = 0 := by
    have h' := hM
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at h'
    have e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M) := by noncomm_ring
    rw [e] at h'
    exact add_eq_left.1 h'
  have hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0 := by
    calc M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi
        = Gi * G * M * Gi + Gi * Mᴴ * (G * Gi) + Gi * Mᴴ * G * M * Gi := by
          rw [hGi1, hGi2]
          noncomm_ring
      _ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring
      _ = 0 := by rw [hK]; noncomm_ring
  have key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0 := by
    rw [hbr]
    simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, hGih]
  refine Eq.trans ?_ (add_zero J)
  rw [← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]
  abel

end Formalism.L2.S.L6.UnitaryStandardVectors
