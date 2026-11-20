import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

/- English proof (translation)
Introduce `o b T`. Establish `hd : finrank ℝ V = d` using `Fact.out`. Set `e : Basis (Fin d) ℝ V` to `Module.finBasisOfFinrankEq ℝ V hd`. Establish `key : ∀ v : Fin d → V, o.volumeForm v = o.volumeForm e * e.det v`. Introduce `v`.

Use `conv_lhs => rw [AlternatingMap.eq_smul_basis_det e o.volumeForm]`. Both sides reduce to the same expression. Establish `hmat : e.toMatrix (fun i => ∑ j, (T i j : ℝ) • b j) = e.toMatrix b * (T.map (Int.cast : ℤ → ℝ))ᵀ`. Use extensionality with `k i`. Simplify using `[Basis.toMatrix_apply, Matrix.mul_apply, map_sum, map_smul, Finset.sum_apply, mul_comm]`.

Rewrite using `[key, key b, Basis.det_apply, Basis.det_apply, hmat, det_mul, det_transpose, Int.cast_det T]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem VolumeFormIntComb.proof : VolumeFormIntComb.Statement V d := by
  intro o b T
  have hd : finrank ℝ V = d := Fact.out
  let e : Basis (Fin d) ℝ V := Module.finBasisOfFinrankEq ℝ V hd
  have key : ∀ v : Fin d → V, o.volumeForm v = o.volumeForm e * e.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e o.volumeForm]
    rfl
  have hmat : e.toMatrix (fun i => ∑ j, (T i j : ℝ) • b j) =
      e.toMatrix b * (T.map (Int.cast : ℤ → ℝ))ᵀ := by
    ext k i
    simp [Basis.toMatrix_apply, Matrix.mul_apply, map_sum, map_smul, Finset.sum_apply,
      mul_comm]
  rw [key, key b, Basis.det_apply, Basis.det_apply, hmat, det_mul, det_transpose,
    Int.cast_det T]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
