import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]`.
-/
theorem matrix_pow_mul_eq_mul_pow_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) (n : ℕ) :
    X ^ n * ε = ε * β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/- English proof (translation)
Set `_ : NormedRing (Matrix (Fin m) (Fin m) ℂ)` to `Matrix.linftyOpNormedRing`. Set `_ : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Conclude with `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X`.
-/
theorem matrix_hasSum_exp {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) (NormedSpace.exp X) := by
  let _ : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

/- English proof (translation)
Set `g : Matrix (Fin m) (Fin m) ℂ →+ Matrix (Fin m) (Fin r) ℂ` to `AddMonoidHom.mk' (fun A => A * ε) (fun A B => Matrix.add_mul A B ε)`. Establish `hg : Continuous g` using `Continuous.matrix_mul continuous_id continuous_const`. Set `g' : Matrix (Fin r) (Fin r) ℂ →+ Matrix (Fin m) (Fin r) ℂ` to `AddMonoidHom.mk' (fun A => ε * A) (fun A B => Matrix.mul_add ε A B)`. Establish `hg' : Continuous g'` using `Continuous.matrix_mul continuous_const continuous_id`. Establish `hL` using `(matrix_hasSum_exp X).map g hg`.

Establish `hR` using `(matrix_hasSum_exp β).map g' hg'`. Establish `key : (g ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) = (g' ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • β ^ n)`. Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp, g, g', AddMonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul, matrix_pow_mul_eq_mul_pow_of_intertwine X ε β h n]`. Rewrite `hL` using `[key]`.

Conclude with `hL.unique hR`.
-/
theorem matrix_exp_mul_eq_mul_exp_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) :
    NormedSpace.exp X * ε = ε * NormedSpace.exp β := by
  let g : Matrix (Fin m) (Fin m) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => A * ε) (fun A B => Matrix.add_mul A B ε)
  have hg : Continuous g := Continuous.matrix_mul continuous_id continuous_const
  let g' : Matrix (Fin r) (Fin r) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => ε * A) (fun A B => Matrix.mul_add ε A B)
  have hg' : Continuous g' := Continuous.matrix_mul continuous_const continuous_id
  have hL := (matrix_hasSum_exp X).map g hg
  have hR := (matrix_hasSum_exp β).map g' hg'
  have key : (g ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) =
      (g' ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • β ^ n) := by
    funext n
    simp only [Function.comp, g, g', AddMonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul,
      matrix_pow_mul_eq_mul_pow_of_intertwine X ε β h n]
  rw [key] at hL
  exact hL.unique hR

/- English proof (translation)
Introduce `m r X ε β h s`. Apply `matrix_exp_mul_eq_mul_exp_of_intertwine` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, h]`.
-/
theorem matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine :
    ∀ (m r : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) (ε : Matrix (Fin m) (Fin r) ℂ)
      (β : Matrix (Fin r) (Fin r) ℂ), X * ε = ε * β →
      ∀ s : ℝ, NormedSpace.exp (s • X) * ε = ε * NormedSpace.exp (s • β) := by
  intro m r X ε β h s
  apply matrix_exp_mul_eq_mul_exp_of_intertwine
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

end GlobalTheory
