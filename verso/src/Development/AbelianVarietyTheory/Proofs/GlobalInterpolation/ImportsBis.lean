import Mathlib
namespace GlobalTheory.LocalRingFurtherFacts

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem main {O : Type} [CommRing O] [IsLocalRing O] {a k : ℕ} {c : O}
    (hc : c ∈ IsLocalRing.maximalIdeal O ^ k) :
    (MvPowerSeries.C : O → MvPowerSeries (Fin a) O) c ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ k := by
  have h1 : Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal x).mp hx
    have := hu.map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O →+* O)
    simpa using this
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

end GlobalTheory.LocalRingFurtherFacts
