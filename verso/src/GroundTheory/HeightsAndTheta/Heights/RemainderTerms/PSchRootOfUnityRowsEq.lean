import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Complex

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootOfUnity_pow_self (k : ℕ) (hk : k ≠ 0) : rootOfUnity k ^ k = 1 :=
  (Complex.isPrimitiveRoot_exp k hk).pow_eq_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootOfUnity_pow_mod (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    rootOfUnity k ^ a = rootOfUnity k ^ (a % k) := by
  conv_lhs => rw [← Nat.mod_add_div a k, pow_add, pow_mul, rootOfUnity_pow_self k hk, one_pow,
    mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
