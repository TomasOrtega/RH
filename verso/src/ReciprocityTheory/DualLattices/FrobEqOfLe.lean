import Mathlib

noncomputable section

open Finset Filter Topology

namespace ReciprocityTheory.PGsh.Up.Det2

/- English proof (translation)
Establish `hM : (Matrix.of fun j k => c j k * (y j / z k)) = Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹`. Use extensionality with `j k`. Simplify using `only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul, map_prod, map_prod]`.

Simplify using `only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem v_det_scaled {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by
  have hM : (Matrix.of fun j k => c j k * (y j / z k)) =
      Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹ := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    map_prod, map_prod]
  simp only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

end ReciprocityTheory.PGsh.Up.Det2
