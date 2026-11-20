import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {n : ℕ}

def cols (x : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun p i => x i p

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem cols_mulVec (x : Fin n → Fin n → ℂ) (c : Fin n → ℂ) : cols x *ᵥ c = ∑ i, c i • x i := by
  funext p
  simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Rewrite using `[cols_mulVec, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem cols_mulVec_single (x : Fin n → Fin n → ℂ) (i : Fin n) : cols x *ᵥ Pi.single i 1 = x i := by
  rw [cols_mulVec, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use extensionality with `p i`. Simplify using `[cols, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem mul_cols (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    A * cols x = cols (fun i => A *ᵥ x i) := by
  ext p i
  simp [cols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use extensionality with `j i`. Rewrite using `[Matrix.mul_assoc, mul_cols]`. Simplify using `[cols, Matrix.mul_apply, herm, dotProduct, Matrix.conjTranspose_apply]`.
-/
theorem gram_cols (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    (cols x)ᴴ * H * cols x = Matrix.of fun j i => herm H (x i) (x j) := by
  ext j i
  rw [Matrix.mul_assoc, mul_cols]
  simp [cols, Matrix.mul_apply, herm, dotProduct, Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite using `[gram_cols]`. Use extensionality with `j i`. Conclude with `hx i j`.
-/
theorem gram_eq {H : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : (cols x)ᴴ * H * cols x = H := by
  rw [gram_cols]
  ext j i
  exact hx i j

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (gram_eq hx)`. Rewrite `h` using `[Matrix.det_mul]`. Rewrite `hH` using `[← h]`. Conclude with `isUnit_of_mul_isUnit_right hH`.
-/
theorem cols_unit {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : IsUnit (cols x).det := by
  have h := congrArg Matrix.det (gram_eq hx)
  rw [Matrix.det_mul] at h
  rw [← h] at hH
  exact isUnit_of_mul_isUnit_right hH

/- English proof (translation)
Establish `hX` using `cols_unit hH hx`. Establish `gx` using `gram_eq hx`. Establish `gy` using `gram_eq hy`. Establish `e1 : (cols x)⁻¹ * cols x = 1` using `Matrix.nonsing_inv_mul _ hX`. Establish `e2 : cols x * (cols x)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hX`.

Use `⟨cols y * (cols x)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `show (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹) = H`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = ((cols x)⁻¹)ᴴ * ((cols x)ᴴ * H * cols x) * (cols x)⁻¹ := by rw [gy, gx]`. Use `_ = (cols x * (cols x)⁻¹)ᴴ * H * (cols x * (cols x)⁻¹) := by`. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = H := by rw [e2]; simp`.

Introduce `i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cols_mulVec_single]`. Use `_ = y i := by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc, e1, Matrix.mul_one, cols_mulVec_single]`.
-/
theorem wittGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x y : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (hy : ∀ i j, herm H (y i) (y j) = H j i) :
    ∃ g ∈ UH H, ∀ i, g *ᵥ x i = y i := by
  have hX := cols_unit hH hx
  have gx := gram_eq hx
  have gy := gram_eq hy
  have e1 : (cols x)⁻¹ * cols x = 1 := Matrix.nonsing_inv_mul _ hX
  have e2 : cols x * (cols x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hX
  refine ⟨cols y * (cols x)⁻¹, ?_, ?_⟩
  · show (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹) = H
    calc (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹)
        = ((cols x)⁻¹)ᴴ * ((cols y)ᴴ * H * cols y) * (cols x)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = ((cols x)⁻¹)ᴴ * ((cols x)ᴴ * H * cols x) * (cols x)⁻¹ := by rw [gy, gx]
      _ = (cols x * (cols x)⁻¹)ᴴ * H * (cols x * (cols x)⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [e2]; simp
  · intro i
    calc (cols y * (cols x)⁻¹) *ᵥ x i = (cols y * (cols x)⁻¹) *ᵥ (cols x *ᵥ Pi.single i 1) := by
          rw [cols_mulVec_single]
      _ = y i := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, e1, Matrix.mul_one, cols_mulVec_single]

/- English proof (translation)
Establish `hX` using `cols_unit hH hx`. Establish `e : A * cols x = B * cols x`. Rewrite using `[mul_cols, mul_cols]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `h i`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem extGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i, A *ᵥ x i = B *ᵥ x i) : A = B := by
  have hX := cols_unit hH hx
  have e : A * cols x = B * cols x := by
    rw [mul_cols, mul_cols]
    congr 1
    funext i
    exact h i
  calc A = A * cols x * (cols x)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
    _ = B := by rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
