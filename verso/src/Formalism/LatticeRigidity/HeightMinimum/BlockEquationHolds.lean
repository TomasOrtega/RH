import Formalism.LatticeRigidity.StatementA

namespace Formalism.SA.P

open Matrix Formalism.SA.A

section Blocks

variable {R : Type} [CommRing R] {m : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
-/
lemma blk_mul_blk (A A' : Matrix (Fin (m+1)) (Fin (m+1)) R) (b c b' c' : Fin (m+1) → R) (d d' : R) :
    blk A b c d * blk A' b' c' d' =
      blk (A * A' + vecMulVec b c') (A *ᵥ b' + d' • b) (c ᵥ* A' + d • c') (c ⬝ᵥ b' + d * d') := by
  unfold blk
  rw [fromBlocks_multiply]
  congr 1
  · ext i j
    simp [Matrix.mul_apply, vecMulVec]
  · ext i j
    simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]
  · ext i j
    simp [Matrix.mul_apply, vecMul, dotProduct]
  · ext i j
    simp [Matrix.mul_apply, dotProduct]

end Blocks

end Formalism.SA.P
