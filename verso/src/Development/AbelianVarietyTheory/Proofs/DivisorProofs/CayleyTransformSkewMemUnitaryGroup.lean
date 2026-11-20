import Mathlib
import Formalism.SatakeDualWeyl.Statement
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.CayleyUnitary

open Formalism.UG

/- English proof (translation)
Unfold `cT`. Rewrite using `[Matrix.map_add _ (map_add σ), Matrix.transpose_add]`.
-/
theorem cT_add' {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A + B) = cT σ A + cT σ B := by
  unfold cT; rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]

/- English proof (translation)
Unfold `cT`. Rewrite using `[Matrix.map_sub _ (map_sub σ), Matrix.transpose_sub]`.
-/
theorem cT_sub' {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A - B) = cT σ A - cT σ B := by
  unfold cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.transpose_sub]

/- English proof (translation)
Introduce `hJ hS hd`. Establish `hneg : cT σ S * J = -(J * S)` using `eq_neg_of_add_eq_zero_left hS`. Establish `hBu : IsUnit (1 - S).det` using `isUnit_iff_ne_zero.mpr hd`. Establish `hBBi : (1 - S) * (1 - S)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hBu`. Establish `h1 : cT σ (1 + S) * J = J * (1 - S)`.

Rewrite using `[cT_add', cT_one, Matrix.add_mul, Matrix.one_mul, hneg, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]`. Establish `h2 : J * (1 + S) = cT σ (1 - S) * J`. Rewrite using `[cT_sub', cT_one, Matrix.sub_mul, Matrix.one_mul, hneg, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]`. Establish `hc : (1 - S) * (1 + S) = (1 + S) * (1 - S)`. Rewrite using `[Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Establish `key : cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J`. Rewrite using `[cT_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT σ (1 - S)⁻¹ * J * ((1 - S) * (1 + S)) * (1 - S)⁻¹ := by`. Rewrite using `[h1]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT σ (1 - S)⁻¹ * (J * (1 + S)) * ((1 - S) * (1 - S)⁻¹) := by`.

Rewrite using `[hc]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by`. Rewrite using `[h2, hBBi, Matrix.mul_one, ← Matrix.mul_assoc, ← cT_mul, hBBi, cT_one, Matrix.one_mul]`. Establish `hdet : ((1 + S) * (1 - S)⁻¹).det ≠ 0`.

Introduce `h0`. Use `congrArg Matrix.det key` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero]`. Conclude with `hJ this.symm`. Use `⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), ?_, rfl⟩` and prove the remaining obligations.

Use `show cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J`. Conclude with `key`.
-/
theorem cayley_mem_UJ {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E) :
    J.det ≠ 0 → cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  intro hJ hS hd
  have hneg : cT σ S * J = -(J * S) := eq_neg_of_add_eq_zero_left hS
  have hBu : IsUnit (1 - S).det := isUnit_iff_ne_zero.mpr hd
  have hBBi : (1 - S) * (1 - S)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have h1 : cT σ (1 + S) * J = J * (1 - S) := by
    rw [cT_add', cT_one, Matrix.add_mul, Matrix.one_mul, hneg, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
  have h2 : J * (1 + S) = cT σ (1 - S) * J := by
    rw [cT_sub', cT_one, Matrix.sub_mul, Matrix.one_mul, hneg, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  have hc : (1 - S) * (1 + S) = (1 + S) * (1 - S) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]; abel
  have key : cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J := by
    rw [cT_mul]
    calc cT σ (1 - S)⁻¹ * cT σ (1 + S) * J * ((1 + S) * (1 - S)⁻¹)
        = cT σ (1 - S)⁻¹ * (cT σ (1 + S) * J) * (1 + S) * (1 - S)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * J * ((1 - S) * (1 + S)) * (1 - S)⁻¹ := by
          rw [h1]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * (J * (1 + S)) * ((1 - S) * (1 - S)⁻¹) := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = J := by
          rw [h2, hBBi, Matrix.mul_one, ← Matrix.mul_assoc, ← cT_mul, hBBi, cT_one, Matrix.one_mul]
  have hdet : ((1 + S) * (1 - S)⁻¹).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ this.symm
  refine ⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), ?_, rfl⟩
  show cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J
  exact key

end GlobalTheory.CayleyUnitary
