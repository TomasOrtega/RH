import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem lead_mul_unique : ∀ (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ r y : R) (n : ℕ) (c c' : C), ξ ∈ nonZeroDivisors R → Lead f ξ r n c → Lead f ξ (y * r) n c' → c' = f y * c := by
  intro R C _ _ f ξ r y n c c' hξ h1 h2
  obtain ⟨s, t, hs, hst, hft⟩ := h1
  obtain ⟨s', t', hs', hst', hft'⟩ := h2
  have hpow : ξ ^ n ∈ nonZeroDivisors R := pow_mem hξ n
  have key : ξ ^ n * (s' * y * t) = ξ ^ n * (s * t') := by
    calc ξ ^ n * (s' * y * t) = s' * y * (s * r) := by rw [hst]; ring
      _ = s * (s' * (y * r)) := by ring
      _ = ξ ^ n * (s * t') := by rw [hst']; ring
  have key2 : s' * y * t = s * t' := by
    have := (mem_nonZeroDivisors_iff.mp hpow).1 (s' * y * t - s * t') (by rw [mul_sub, key, sub_self])
    exact sub_eq_zero.mp (this)
  have key3 := congrArg f key2
  simp only [map_mul, hft, hft'] at key3
  have hne : f s * f s' ≠ 0 := mul_ne_zero hs hs'
  apply mul_left_cancel₀ hne
  linear_combination -key3

end GlobalTheory.DetInv
