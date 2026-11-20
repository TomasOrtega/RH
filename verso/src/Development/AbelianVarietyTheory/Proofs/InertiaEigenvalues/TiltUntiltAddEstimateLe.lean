import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltInjectiveAndDvdOfNormLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

/- English proof (translation)
Take `⟨h1, -, hmul, -, hle1, -, hadd, -⟩` from `GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l`. Take `⟨u, rfl⟩` from `(GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le l).2 x y hxy`. Establish `hsum : y * u + y = y * (u + 1)` using `by ring`. Rewrite using `[hsum, hmul, hmul]`. Prove the components needed by the constructor for the conclusion.

Establish `key : sh y * sh (u + 1) - sh y * sh u - sh y = sh y * (sh (u + 1) - sh u - sh (1 : Fl l))` using `by rw [h1]; ring`. Rewrite using `[key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]`. Conclude with `mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tiltUntilt_add_estimate_of_norm_le (l : ℕ) [Fact l.Prime] (x y : Fl l) (hxy : ‖sh x‖ ≤ ‖sh y‖) :
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * ‖sh y‖ ∧ ‖sh (x + y)‖ ≤ ‖sh y‖ := by
  obtain ⟨h1, -, hmul, -, hle1, -, hadd, -⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨u, rfl⟩ := (GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le l).2 x y hxy
  have hsum : y * u + y = y * (u + 1) := by ring
  rw [hsum, hmul, hmul]
  constructor
  · have key : sh y * sh (u + 1) - sh y * sh u - sh y
        = sh y * (sh (u + 1) - sh u - sh (1 : Fl l)) := by rw [h1]; ring
    rw [key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]
    exact mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)
  · rw [norm_mul]
    calc ‖sh y‖ * ‖sh (u + 1)‖ ≤ ‖sh y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hle1 _) (norm_nonneg _)
      _ = ‖sh y‖ := mul_one _

/- English proof (translation)
Introduce `l _ r x y hx hy`. Establish `hl : 0 ≤ ‖(l : ℂ_[l])‖` using `norm_nonneg _`. Break down `le_total ‖sh x‖ ‖sh y‖ with h | h` into its components or cases. Take `⟨h1, h2⟩` from `tiltUntilt_add_estimate_of_norm_le l x y h`. Conclude with `⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩`.

Take `⟨h1, h2⟩` from `tiltUntilt_add_estimate_of_norm_le l y x h`. Rewrite using `[add_comm x y]`. Use `⟨?_, h2.trans hx⟩` and prove the remaining obligations. Establish `e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x` using `by ring`. Rewrite using `[e]`.

Conclude with `h1.trans (mul_le_mul_of_nonneg_left hx hl)`.
-/
theorem sh_add_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r →
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  intro l _ r x y hx hy
  have hl : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  rcases le_total ‖sh x‖ ‖sh y‖ with h | h
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l x y h
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l y x h
    rw [add_comm x y]
    refine ⟨?_, h2.trans hx⟩
    have e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x := by ring
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hx hl)

end GlobalTheory.PSer
