import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

namespace GlobalTheory.HilbFam

/- English proof (translation)
Introduce `τ c t hτ`. Establish `h1 : ContinuousAt (fun z : ℂ => ‖1 + z * c‖) 0` using `by fun_prop`. Establish `h2' : ContinuousAt (fun z : ℂ => τ + t * z / (1 + z * c)) 0`. Use `continuousAt_const.add (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp))` and prove the remaining obligations. Establish `h2 : ContinuousAt (fun z : ℂ => (τ + t * z / (1 + z * c)).im) 0` using `Complex.continuous_im.continuousAt.comp h2'`.

Establish `e1 : ∀ᶠ z in nhds (0 : ℂ), (1 / 2 : ℝ) < ‖1 + z * c‖` using `h1.eventually (lt_mem_nhds (by norm_num))`. Establish `e2 : ∀ᶠ z in nhds (0 : ℂ), τ.im / 2 < (τ + t * z / (1 + z * c)).im` using `h2.eventually (lt_mem_nhds (by simp; linarith))`. Take `⟨r, hr, h⟩` from `Metric.eventually_nhds_iff.1 (e1.and e2)`. Use `⟨r, hr, fun z hz => ?_⟩` and prove the remaining obligations. Use `h (y := z) (by simpa using hz)` as an intermediate fact.

Conclude with `⟨this.1.le, this.2.le⟩`.
-/
theorem exists_radius_moebius_perturbation :
    ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  intro τ c t hτ
  have h1 : ContinuousAt (fun z : ℂ => ‖1 + z * c‖) 0 := by fun_prop
  have h2' : ContinuousAt (fun z : ℂ => τ + t * z / (1 + z * c)) 0 := by
    refine continuousAt_const.add (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp))
  have h2 : ContinuousAt (fun z : ℂ => (τ + t * z / (1 + z * c)).im) 0 :=
    Complex.continuous_im.continuousAt.comp h2'
  have e1 : ∀ᶠ z in nhds (0 : ℂ), (1 / 2 : ℝ) < ‖1 + z * c‖ :=
    h1.eventually (lt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ z in nhds (0 : ℂ), τ.im / 2 < (τ + t * z / (1 + z * c)).im :=
    h2.eventually (lt_mem_nhds (by simp; linarith))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨r, hr, fun z hz => ?_⟩
  have := h (y := z) (by simpa using hz)
  exact ⟨this.1.le, this.2.le⟩

end GlobalTheory.HilbFam
