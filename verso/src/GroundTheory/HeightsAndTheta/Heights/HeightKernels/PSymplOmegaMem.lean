import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOmegaMem

/- English proof (translation)
Rewrite using `[symplOmega, dotProduct_mulVec, Matrix.mul_apply]`. Both sides reduce to the same expression.
-/
theorem mul_J_mul_transpose_apply {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by
  rw [symplOmega, dotProduct_mulVec, Matrix.mul_apply]
  rfl

end PSymplOmegaMem

/- English proof (translation)
Introduce `R _ l _ _ M`. Rewrite using `[SymplecticGroup.mem_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x y`. Rewrite using `[← PSymplOmegaMem.mul_J_mul_transpose_apply, h]`.

Introduce `h`. Use extensionality with `x y`. Rewrite using `[PSymplOmegaMem.mul_J_mul_transpose_apply, h]`.
-/
theorem SymplOmegaMem.proof : SymplOmegaMem.Statement := by
  intro R _ l _ _ M
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h x y
    rw [← PSymplOmegaMem.mul_J_mul_transpose_apply, h]
  · intro h
    ext x y
    rw [PSymplOmegaMem.mul_J_mul_transpose_apply, h]

end GroundTheory.Heights₂.Heights
