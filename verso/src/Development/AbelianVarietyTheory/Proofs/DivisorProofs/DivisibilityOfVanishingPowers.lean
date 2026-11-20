import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro r _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `r h`. Establish `hr0 : ∀ i, f i r = 0`. Introduce `i`. Take `⟨s, hs, t, ht⟩` from `h i`. Establish `h1 : f i (s * r) = 0`.

Rewrite using `[ht, map_mul, map_pow, hf i, zero_pow (Nat.succ_ne_zero n), zero_mul]`. Rewrite `h1` using `[map_mul]`. Conclude with `(mul_eq_zero.mp h1).resolve_left hs`. Take `⟨r1, rfl⟩` from `hker r hr0`. Establish `h2 : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r1`.

Introduce `i`. Take `⟨s, hs, t, ht⟩` from `h i`. Use `⟨s, hs, t, ?_⟩` and prove the remaining obligations. Establish `: ξ * (s * r1) = ξ * (ξ ^ n * t)`. Rewrite using `[← mul_assoc, mul_comm ξ s, mul_assoc, ht]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_cancel_left_mem_nonZeroDivisors hξ).mp this`. Take `⟨u, hu⟩` from `ih r1 h2`. Conclude with `⟨u, by rw [hu]; ring⟩`.
-/
theorem DetInv.dvd_pow_of_local_dvd_pow (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R)
    (hξ : ξ ∈ nonZeroDivisors R) (hf : ∀ i, f i ξ = 0) (hker : ∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) :
    ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r h
    have hr0 : ∀ i, f i r = 0 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      have h1 : f i (s * r) = 0 := by
        rw [ht, map_mul, map_pow, hf i, zero_pow (Nat.succ_ne_zero n), zero_mul]
      rw [map_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hs
    obtain ⟨r1, rfl⟩ := hker r hr0
    have h2 : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r1 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      refine ⟨s, hs, t, ?_⟩
      have : ξ * (s * r1) = ξ * (ξ ^ n * t) := by
        rw [← mul_assoc, mul_comm ξ s, mul_assoc, ht]; ring
      exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp this
    obtain ⟨u, hu⟩ := ih r1 h2
    exact ⟨u, by rw [hu]; ring⟩

/- English proof (translation)
The claim follows from `@DetInv.dvd_pow_of_local_dvd_pow`.
-/
example : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r :=
  @DetInv.dvd_pow_of_local_dvd_pow

end GlobalTheory
