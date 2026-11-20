import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PSymplGcd

/- English proof (translation)
Take `⟨a', ha'⟩` from `Int.gcd_dvd_left a b`. Take `⟨b', hb'⟩` from `Int.gcd_dvd_right a b`. Use `⟨(Int.gcd a b : ℤ), a', b', Int.gcdA a b, Int.gcdB a b, ha', hb', ?_⟩` and prove the remaining obligations. Establish `h` using `Int.gcd_eq_gcd_ab a b`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises.

Take the linear combination `(-Int.gcdA a b) * ha' - Int.gcdB a b * hb' - h`.
-/
theorem of_gcd_ne_zero (a b : ℤ) (hc : (Int.gcd a b : ℤ) ≠ 0) :
    ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1 := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  refine ⟨(Int.gcd a b : ℤ), a', b', Int.gcdA a b, Int.gcdB a b, ha', hb', ?_⟩
  have h := Int.gcd_eq_gcd_ab a b
  apply mul_left_cancel₀ hc
  linear_combination (-Int.gcdA a b) * ha' - Int.gcdB a b * hb' - h

end PSymplGcd

/- English proof (translation)
Introduce `a b`. Distinguish the cases in `hc : (Int.gcd a b : ℤ) = 0`. Establish `h0 : Int.gcd a b = 0` using `by exact_mod_cast hc`. Take `⟨rfl, rfl⟩` from `Int.gcd_eq_zero_iff.mp h0`. Conclude with `⟨0, 1, 0, 1, 0, by ring, by ring, by ring⟩`.

Conclude with `PSymplGcd.of_gcd_ne_zero a b hc`.
-/
theorem SymplGcd.proof : SymplGcd.Statement := by
  intro a b
  by_cases hc : (Int.gcd a b : ℤ) = 0
  · have h0 : Int.gcd a b = 0 := by exact_mod_cast hc
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
    exact ⟨0, 1, 0, 1, 0, by ring, by ring, by ring⟩
  · exact PSymplGcd.of_gcd_ne_zero a b hc

end GroundTheory.Heights₂.Heights
