import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem dvd_of_twisted_eq :
    ∀ (R : Type) [CommRing R] (ψ : R →+* R) (m Δ Δs Δ' g b : R), m ∈ nonZeroDivisors R →
      Δ * Δs = m → Δ = g * ψ Δ → Δ' = g * b * ψ Δ' →
      (∀ z w : R, z * ψ m = m * w * ψ z → m ∣ z) → Δ ∣ Δ' := by
  intro R _ ψ m Δ Δs Δ' g b hm hmul hΔ hΔ' key
  have hz : (Δ' * Δs) * ψ m = m * b * ψ (Δ' * Δs) := by
    have h1 : Δ' * ψ Δ = b * ψ Δ' * Δ := by
      calc Δ' * ψ Δ = (g * b * ψ Δ') * ψ Δ := by rw [← hΔ']
        _ = b * ψ Δ' * (g * ψ Δ) := by ring
        _ = b * ψ Δ' * Δ := by rw [← hΔ]
    rw [← hmul, map_mul, map_mul]
    calc Δ' * Δs * (ψ Δ * ψ Δs) = (Δ' * ψ Δ) * (Δs * ψ Δs) := by ring
      _ = (b * ψ Δ' * Δ) * (Δs * ψ Δs) := by rw [h1]
      _ = Δ * Δs * b * (ψ Δ' * ψ Δs) := by ring
  obtain ⟨c, hc⟩ := key _ _ hz
  refine ⟨c, ?_⟩
  have hzero : (Δ' - Δ * c) * m = 0 := by
    have : (Δ' - Δ * c) * Δs = 0 := by
      rw [sub_mul, hc, ← hmul]; ring
    calc (Δ' - Δ * c) * m = ((Δ' - Δ * c) * Δs) * Δ := by rw [← hmul]; ring
      _ = 0 := by rw [this, zero_mul]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hm) _ hzero)

end GlobalTheory.DetInv
