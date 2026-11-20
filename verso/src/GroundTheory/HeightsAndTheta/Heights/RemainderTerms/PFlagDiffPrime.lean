import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

namespace FlagDiffPrime

variable {σ : Type} [DecidableEq σ]

def collapse (a b : σ) : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ :=
  aeval fun i => if i = a then X b else X i

/- English proof (translation)
Simplify using `[collapse]`.
-/
theorem collapse_X_sub (a b : σ) : collapse a b (X a - X b : MvPolynomial σ ℚ) = 0 := by
  simp [collapse]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C c => simp [collapse]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `dvd_add hp hq`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`. Establish `e : p * X i - collapse a b p * collapse a b (X i) = (p - collapse a b p) * X i + collapse a b p * (X i - collapse a b (X i))` using `by ring`. Rewrite using `[e]`. Use `dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)` and prove the remaining obligations.

Distinguish the cases in `h : i = a`. Rewrite using `[h]`. Simplify using `[collapse]`. Simplify using `[collapse, h]`.
-/
theorem dvd_sub_collapse (a b : σ) (Q : MvPolynomial σ ℚ) :
    (X a - X b : MvPolynomial σ ℚ) ∣ Q - collapse a b Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [collapse]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have e : p * X i - collapse a b p * collapse a b (X i) =
        (p - collapse a b p) * X i + collapse a b p * (X i - collapse a b (X i)) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    by_cases h : i = a
    · rw [h]; simp [collapse]
    · simp [collapse, h]

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Rewrite using `[map_mul, collapse_X_sub, zero_mul]`.
-/
theorem collapse_eq_zero_of_dvd (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, collapse_X_sub, zero_mul]

/- English proof (translation)
Simplify `dvd_sub_collapse a b P` using `[h]`.
-/
theorem dvd_of_collapse_eq_zero (a b : σ) {P : MvPolynomial σ ℚ}
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by
  simpa [h] using dvd_sub_collapse a b P

/- English proof (translation)
Introduce `σ _ a b hab`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_ne_zero]`. Conclude with `fun h => hab (X_injective h)`. Introduce `hu`.

Establish `hu'` using `hu.map (collapse a b)`. Rewrite `hu'` using `[collapse_X_sub]`. Conclude with `not_isUnit_zero hu'`. Introduce `A B h`. Establish `h0` using `collapse_eq_zero_of_dvd a b h`.

Rewrite `h0` using `[map_mul, mul_eq_zero]`. Break down `h0 with h0 | h0` into its components or cases. Conclude with `Or.inl (dvd_of_collapse_eq_zero a b h0)`. Conclude with `Or.inr (dvd_of_collapse_eq_zero a b h0)`.
-/
theorem proof : FlagDiffPrime.Statement := by
  intro σ _ a b hab
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_ne_zero]
    exact fun h => hab (X_injective h)
  · intro hu
    have hu' := hu.map (collapse a b)
    rw [collapse_X_sub] at hu'
    exact not_isUnit_zero hu'
  · intro A B h
    have h0 := collapse_eq_zero_of_dvd a b h
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Or.inl (dvd_of_collapse_eq_zero a b h0)
    · exact Or.inr (dvd_of_collapse_eq_zero a b h0)

end FlagDiffPrime

end

end RestTerms

end GroundTheory.Heights₂.Heights
