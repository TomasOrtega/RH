import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticDiffOp

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

variable {n : ℕ}

section Integrable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def ofIntegrable {h : E → ℂ} (hh : Integrable h) : 𝓢'(E, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (hh.toL1 h)

end Integrable

/- English proof (translation)
Establish `hK` using `(hu.mono_set hφΩ).integrableOn_isCompact hφc.isCompact`. Establish `hind` using `hK.integrable_indicator (isClosed_tsupport _).measurableSet`. Establish `h` using `hind.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 φ) φ.continuous.aestronglyMeasurable (ae_of_all _ fun x ↦ SchwartzMap.norm_le_seminorm ℝ _ _)`. Use `h.congr (ae_of_all _ fun x ↦ ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`.

Distinguish the cases in `hx : x ∈ tsupport φ`. Rewrite using `[Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]`.
-/
theorem integrable_smul_of_locallyIntegrableOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {u : E → ℂ} (hu : LocallyIntegrableOn u Ω) {φ : 𝓢(E, ℂ)} (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) : Integrable (fun x ↦ φ x • u x) := by
  have hK := (hu.mono_set hφΩ).integrableOn_isCompact hφc.isCompact
  have hind := hK.integrable_indicator (isClosed_tsupport _).measurableSet
  have h := hind.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 φ) φ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x ↦ SchwartzMap.norm_le_seminorm ℝ _ _)
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul]
  by_cases hx : x ∈ tsupport φ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end

end GroundTheory.Automorphic.Sobolev
