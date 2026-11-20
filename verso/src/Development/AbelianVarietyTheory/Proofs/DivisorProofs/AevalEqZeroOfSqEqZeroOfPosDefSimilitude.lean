import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.SimNormSq

open Polynomial

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_right hq`. Consider the case `monomial n a`. Rewrite using `[aeval_monomial]`.

Conclude with `(Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)`.
-/
theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : A} (h : Commute y x) (p : R[X]) : Commute y (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)

/- English proof (translation)
Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Matrix.zero_mulVec]`. Assume the negation of the conclusion as `hne`. Establish `hpos` using `hH.dotProduct_mulVec_pos hne`.

Rewrite `hpos` using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, Matrix.zero_mulVec, dotProduct_zero]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem eq_zero_of_conjTranspose_mul_mul_eq_zero {n : ℕ} {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (h : Aᴴ * H * A = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  by_contra hne
  have hpos := hH.dotProduct_mulVec_pos hne
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
    Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.SimNormSq

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `n H M s hH hs hM P hP`. Establish `hdet : IsUnit H.det` using `(Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit`. Establish `hHinv : H⁻¹ * H = 1` using `Matrix.nonsing_inv_mul H hdet`. Establish `hHinv' : H * H⁻¹ = 1` using `Matrix.mul_nonsing_inv H hdet`. Establish `hHh : Hᴴ = H` using `hH.1`.

Establish `hHih : (H⁻¹)ᴴ = H⁻¹` using `by rw [conjTranspose_nonsing_inv, hHh]`. Establish `hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A` using `fun A => by`. Rewrite using `[← Matrix.mul_assoc, hHinv, Matrix.one_mul]`. Establish `hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A` using `fun A => by`. Rewrite using `[← Matrix.mul_assoc, hHinv', Matrix.one_mul]`.

Establish `hM' : Mᴴ * (H * M) = (s : ℂ) • H` using `by rw [← Matrix.mul_assoc]; exact hM`. Use `set D := H⁻¹ * Mᴴ * H with hD`. Establish `hDM : D * M = (s : ℂ) • 1`. Rewrite using `[hD]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[hM', Matrix.mul_smul, hHinv]`. Establish `hs0 : (s : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`. Establish `hMD : M * D = (s : ℂ) • 1`. Establish `h1 : ((s : ℂ)⁻¹ • D) * M = 1`. Rewrite using `[Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]`.

Establish `h2` using `mul_eq_one_comm.mp h1`. Rewrite `h2` using `[Matrix.mul_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, mul_inv_cancel₀ hs0, one_smul]`. Use `_ = (s : ℂ) • 1 := by rw [h2]`.

Establish `hcomm : Commute D M` using `by show D * M = M * D`. Rewrite using `[hDM, hMD]`. Establish `hall : ∀ Y, Commute Y M → Commute Y (aeval M P)` using `fun Y hY => SimNormSq.commute_aeval_of_commute hY P`. Establish `hDW` using `hall D hcomm`. Generalize the expression as in `hW : aeval M P = W at hP hDW ⊢`.

Establish `key : Commute (H⁻¹ * Wᴴ * H) M`. Establish `h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ))`. Establish `h0` using `congrArg conjTranspose hDW.eq`. Simplify using `only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih, Matrix.mul_assoc] at h0`. Conclude with `h0`.

Use `show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hHinv, Matrix.mul_one]`. Use `_ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]`. Use `_ = M * (H⁻¹ * Wᴴ * H) := by`.

Simplify using `only [Matrix.mul_assoc, hc]`. Establish `hXW : Commute (H⁻¹ * Wᴴ * H) W`. Establish `h4` using `hall _ key`. Rewrite `h4` using `[hW]`. Then use the resulting hypothesis. Establish `hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih, Matrix.mul_assoc, hc]`. Use `_ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]`. Use `_ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]`. Establish `hX0` using `SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX`.

Establish `hW2 : Wᴴ * H * W = 0`. Establish `h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W` using `by simp only [Matrix.mul_assoc, hc']`. Rewrite using `[← h3, hX0, Matrix.mul_zero]`. Conclude with `SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2`.
-/
theorem aeval_eq_zero_of_mul_self_eq_zero_of_similitude :
    ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s →
      Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ,
        Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  intro n H M s hH hs hM P hP
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHh : Hᴴ = H := hH.1
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [conjTranspose_nonsing_inv, hHh]
  have hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv, Matrix.one_mul]
  have hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv', Matrix.one_mul]
  have hM' : Mᴴ * (H * M) = (s : ℂ) • H := by rw [← Matrix.mul_assoc]; exact hM
  set D := H⁻¹ * Mᴴ * H with hD
  have hDM : D * M = (s : ℂ) • 1 := by
    rw [hD]; simp only [Matrix.mul_assoc]; rw [hM', Matrix.mul_smul, hHinv]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hMD : M * D = (s : ℂ) • 1 := by
    have h1 : ((s : ℂ)⁻¹ • D) * M = 1 := by
      rw [Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc M * D = (s : ℂ) • ((s : ℂ)⁻¹ • (M * D)) := by
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = (s : ℂ) • 1 := by rw [h2]
  have hcomm : Commute D M := by
    show D * M = M * D
    rw [hDM, hMD]
  have hall : ∀ Y, Commute Y M → Commute Y (aeval M P) := fun Y hY =>
    SimNormSq.commute_aeval_of_commute hY P
  have hDW := hall D hcomm
  generalize hW : aeval M P = W at hP hDW ⊢
  have key : Commute (H⁻¹ * Wᴴ * H) M := by
    have h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ)) := by
      have h0 := congrArg conjTranspose hDW.eq
      simp only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
        Matrix.mul_assoc] at h0
      exact h0
    show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)
    calc H⁻¹ * Wᴴ * H * M = H⁻¹ * (Wᴴ * (H * (M * H⁻¹))) * H := by
          simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
      _ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]
      _ = M * (H⁻¹ * Wᴴ * H) := by
          simp only [Matrix.mul_assoc, hc]
  have hXW : Commute (H⁻¹ * Wᴴ * H) W := by
    have h4 := hall _ key
    rwa [hW] at h4
  have hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0 := by
    calc (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W)
        = Wᴴ * H * (W * (H⁻¹ * Wᴴ * H)) * W := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
            Matrix.mul_assoc, hc]
      _ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]
      _ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]
  have hX0 := SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX
  have hW2 : Wᴴ * H * W = 0 := by
    have h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W := by simp only [Matrix.mul_assoc, hc']
    rw [← h3, hX0, Matrix.mul_zero]
  exact SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2

end GlobalTheory
