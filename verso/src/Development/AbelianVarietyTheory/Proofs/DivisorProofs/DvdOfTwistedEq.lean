import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Introduce `R _ ψ m Δ Δs Δ' g b hm hmul hΔ hΔ' key`. Establish `hz : (Δ' * Δs) * ψ m = m * b * ψ (Δ' * Δs)`. Establish `h1 : Δ' * ψ Δ = b * ψ Δ' * Δ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hmul, map_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨c, hc⟩` from `key _ _ hz`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hzero : (Δ' - Δ * c) * m = 0`. Establish `: (Δ' - Δ * c) * Δs = 0`.

Rewrite using `[sub_mul, hc, ← hmul]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Conclude with `sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hm) _ hzero)`.
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
