import Mathlib
namespace GlobalTheory.LocalRingFurtherFacts

/- English proof (translation)
Establish `h1 : Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O) ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Apply `(IsLocalRing.mem_maximalIdeal x).mp hx` to reduce the goal to its premises. Use `hu.map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O →+* O)` as an intermediate fact. Simplify using `using this`. Establish `h2` using `Ideal.mem_map_of_mem (MvPowerSeries.C : O →+* MvPowerSeries (Fin a) O) hc`. Rewrite `h2` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono h1 k h2`.
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
