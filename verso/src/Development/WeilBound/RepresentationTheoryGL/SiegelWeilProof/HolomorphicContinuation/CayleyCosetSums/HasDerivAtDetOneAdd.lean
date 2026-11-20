import Mathlib

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.Rg.Sw.HSt

/- English proof (translation)
Use `set p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det with hp`. Establish `e : (fun s : ℂ => (1 + s • M).det) = fun s => p.eval s`. Use function extensionality and compare the values at `s`. Rewrite using `[hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [mul_comm]`. Rewrite using `[e]`. Establish `h` using `p.hasDerivAt 0`.

Rewrite `h` using `[hp, Matrix.derivative_det_one_add_X_smul]`. Then use the resulting hypothesis.
-/
theorem hasDerivAt_det_one_add {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • M).det) M.trace 0 := by
  set p : ℂ[X] := (1 + (X : ℂ[X]) • M.map C).det with hp
  have e : (fun s : ℂ => (1 + s • M).det) = fun s => p.eval s := by
    funext s
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp [mul_comm]
  rw [e]
  have h := p.hasDerivAt 0
  rwa [hp, Matrix.derivative_det_one_add_X_smul] at h

/- English proof (translation)
Establish `e : (fun s : ℂ => (A + s • X).det) = fun s => A.det * (1 + s • (A⁻¹ * X)).det`. Use function extensionality and compare the values at `s`. Rewrite using `[← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]`. Rewrite using `[e]`. Conclude with `(hasDerivAt_det_one_add (A⁻¹ * X)).const_mul _`.
-/
theorem hasDerivAt_det_add {ι : Type} [Fintype ι] [DecidableEq ι] (A X : Matrix ι ι ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun s : ℂ => (A + s • X).det) (A.det * (A⁻¹ * X).trace) 0 := by
  have e : (fun s : ℂ => (A + s • X).det) = fun s => A.det * (1 + s • (A⁻¹ * X)).det := by
    funext s
    rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [e]
  exact (hasDerivAt_det_one_add (A⁻¹ * X)).const_mul _

end PositivityTheory.Rg.Sw.HSt
