import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

/- English proof (translation)
Introduce `ι _ f S hf hS ⟨y0, hy0⟩`. Establish `hn : (0 : ℝ) < Fintype.card ι`. Conclude with `Fintype.card_pos_iff.2 ⟨y0⟩` after adjusting the coercions. Establish `key : Real.sqrt (Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ y, f y ^ 2) = Real.sqrt (∑ y, f y ^ 2)`. Rewrite using `[← Real.sqrt_mul hn.le, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]`.

Establish `h1 : f y0 ^ 2 ≤ ∑ y, f y ^ 2` using `Finset.single_le_sum (f := fun y => f y ^ 2) (fun y _ => sq_nonneg (f y)) (Finset.mem_univ y0)`. Establish `h2 : f y0 ≤ Real.sqrt (∑ y, f y ^ 2)`. Rewrite using `[← Real.sqrt_sq (hf y0)]`. Conclude with `Real.sqrt_le_sqrt h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem netSup : ReciprocityTheory.ChartRestriction.G.TB.NetSupSt := by
  intro ι _ f S hf hS ⟨y0, hy0⟩
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨y0⟩
  have key : Real.sqrt (Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ y, f y ^ 2)
      = Real.sqrt (∑ y, f y ^ 2) := by
    rw [← Real.sqrt_mul hn.le, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  have h1 : f y0 ^ 2 ≤ ∑ y, f y ^ 2 :=
    Finset.single_le_sum (f := fun y => f y ^ 2) (fun y _ => sq_nonneg (f y)) (Finset.mem_univ y0)
  have h2 : f y0 ≤ Real.sqrt (∑ y, f y ^ 2) := by
    rw [← Real.sqrt_sq (hf y0)]
    exact Real.sqrt_le_sqrt h1
  calc S ≤ 4 * f y0 := by linarith
    _ ≤ 4 * Real.sqrt (∑ y, f y ^ 2) := by linarith
    _ = _ := by rw [mul_assoc, key]

end PI.UnitaryGroupMassFormula.TBNum
