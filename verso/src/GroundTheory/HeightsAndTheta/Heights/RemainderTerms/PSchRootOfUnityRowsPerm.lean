import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Introduce `k l π hk hl`. Establish `hk0 : k ≠ 0` using `Nat.pos_iff_ne_zero.mp hk`. Establish `hζk : rootOfUnity k ^ k = 1`. Unfold `rootOfUnity`. Conclude with `(Complex.isPrimitiveRoot_exp k hk0).pow_eq_one`.

Establish `hmod : ∀ j n : ℕ, rootOfUnity k ^ (j * n) = rootOfUnity k ^ (j * (n % k))`. Introduce `j n`. Use `conv_lhs => rw [← Nat.mod_add_div n k]`. Rewrite using `[mul_add, pow_add, mul_left_comm j k, pow_mul (rootOfUnity k) k, hζk, one_pow, mul_one]`. Establish `hM : (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)) = (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).submatrix π id`.

Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, id]`. Rewrite using `[hmod, hl i]`. Rewrite using `[hM, Matrix.det_permute]`.
-/
theorem SchRootOfUnityRowsPerm.proof : SchRootOfUnityRowsPerm.Statement := by
  intro k l π hk hl
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hζk : rootOfUnity k ^ k = 1 := by
    unfold rootOfUnity
    exact (Complex.isPrimitiveRoot_exp k hk0).pow_eq_one
  have hmod : ∀ j n : ℕ, rootOfUnity k ^ (j * n) = rootOfUnity k ^ (j * (n % k)) := by
    intro j n
    conv_lhs => rw [← Nat.mod_add_div n k]
    rw [mul_add, pow_add, mul_left_comm j k, pow_mul (rootOfUnity k) k, hζk, one_pow, mul_one]
  have hM : (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)) =
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).submatrix π id := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    rw [hmod, hl i]
  rw [hM, Matrix.det_permute]

end GroundTheory.Heights₂.Heights.RestTerms
