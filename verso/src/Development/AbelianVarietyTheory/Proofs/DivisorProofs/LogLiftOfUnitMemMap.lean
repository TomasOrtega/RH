import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

namespace GlobalTheory.DI

set_option autoImplicit false in

/- English proof (translation)
Introduce `K Kt _ _ p _ _ π ι F s At hflat hF g hg hmem hinv`. Take `⟨z, hz, rfl⟩` from `Subring.mem_map.mp hmem`. Take `⟨y, hy, hyz⟩` from `Subring.mem_map.mp hinv`. Unfold `_root_.GlobalTheory.DI.LogLift`. Use `⟨z, rfl, fun i hi => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw, hFw⟩` from `hF i hi z hz`. Use `⟨y ^ p * w, Subring.mem_map.mpr ⟨y ^ p * w, At.mul_mem (At.pow_mem hy p) hw, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h0 : (p : Kt) * (w - z ^ p * y ^ p * w) = 0`. Rewrite using `[hflat.ann]`. Simplify using `only [map_sub, map_mul, map_pow, hyz]`.

Rewrite using `[← mul_pow, mul_inv_cancel₀ hg, one_pow, one_mul, sub_self]`. Rewrite using `[hFw]`. Take the linear combination `h0`.
-/
theorem _root_.GlobalTheory.DI.logLift_of_unit_mem_map : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (At : Subring Kt), _root_.GlobalTheory.DI.IsFlatLift p π →
    (∀ i ∈ s, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w) → ∀ g : K, g ≠ 0 → g ∈ At.map π →
    g⁻¹ ∈ At.map π → _root_.GlobalTheory.DI.LogLift p π F s (At.map π : Set K) g := by
  intro K Kt _ _ p _ _ π ι F s At hflat hF g hg hmem hinv
  obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hmem
  obtain ⟨y, hy, hyz⟩ := Subring.mem_map.mp hinv
  unfold _root_.GlobalTheory.DI.LogLift
  refine ⟨z, rfl, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi z hz
  refine ⟨y ^ p * w, Subring.mem_map.mpr ⟨y ^ p * w, At.mul_mem (At.pow_mem hy p) hw, rfl⟩, ?_⟩
  have h0 : (p : Kt) * (w - z ^ p * y ^ p * w) = 0 := by
    rw [hflat.ann]
    simp only [map_sub, map_mul, map_pow, hyz]
    rw [← mul_pow, mul_inv_cancel₀ hg, one_pow, one_mul, sub_self]
  rw [hFw]
  linear_combination h0

end GlobalTheory.DI
