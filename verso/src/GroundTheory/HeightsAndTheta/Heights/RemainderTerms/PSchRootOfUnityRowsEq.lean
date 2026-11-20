import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Complex

/- English proof (translation)
The claim follows from `(Complex.isPrimitiveRoot_exp k hk).pow_eq_one`.
-/
theorem rootOfUnity_pow_self (k : ℕ) (hk : k ≠ 0) : rootOfUnity k ^ k = 1 :=
  (Complex.isPrimitiveRoot_exp k hk).pow_eq_one

/- English proof (translation)
Use `conv_lhs => rw [← Nat.mod_add_div a k, pow_add, pow_mul, rootOfUnity_pow_self k hk, one_pow, mul_one]`.
-/
theorem rootOfUnity_pow_mod (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    rootOfUnity k ^ a = rootOfUnity k ^ (a % k) := by
  conv_lhs => rw [← Nat.mod_add_div a k, pow_add, pow_mul, rootOfUnity_pow_self k hk, one_pow,
    mul_one]

/- English proof (translation)
Introduce `k l i i' hne hmod`. Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `i.elim0`. Apply `Matrix.det_zero_of_row_eq hne` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[pow_mul', pow_mul', rootOfUnity_pow_mod k hk (l i), rootOfUnity_pow_mod k hk (l i'), hmod]`.
-/
theorem SchRootOfUnityRowsEq.proof : SchRootOfUnityRowsEq.Statement := by
  intro k l i i' hne hmod
  have hk : k ≠ 0 := by
    rintro rfl
    exact i.elim0
  apply Matrix.det_zero_of_row_eq hne
  funext j
  simp only [Matrix.of_apply]
  rw [pow_mul', pow_mul', rootOfUnity_pow_mod k hk (l i), rootOfUnity_pow_mod k hk (l i'), hmod]

end GroundTheory.Heights₂.Heights.RestTerms
