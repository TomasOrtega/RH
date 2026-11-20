import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Introduce `k B _ _ _ _ _ hB`. Establish `hdim : ringKrullDim B = 1`. Apply `eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_` to reduce the goal to its premises. Rewrite using `[← Nat.cast_one, ← Ring.krullDimLE_iff] infer_instance`. Establish `h'' : ringKrullDim B ≤ 0` using `Order.le_of_lt_succ h'`.

Rewrite `h''` using `[← Nat.cast_zero, ← Ring.krullDimLE_iff]`. Conclude with `Ring.KrullDimLE.isField_of_isDomain`. Conclude with `GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B (FractionRing B) hdim`.
-/
theorem UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType :
    ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → IsFunctionField k (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B (FractionRing B) hdim
