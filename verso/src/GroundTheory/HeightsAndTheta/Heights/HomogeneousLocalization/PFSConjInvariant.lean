import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

namespace SectionsLatticeFS

/- English proof (translation)
Introduce `N`. Set `cv : (Fin N → ℂ) → (Fin N → ℂ)` to `fun z k => starRingEnd ℂ (z k)`. Establish `hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume` using `LinearIsometryEquiv.measurePreserving Complex.conjLIE`. Establish `hcv : MeasurePreserving cv volume volume` using `volume_preserving_pi fun _ => hc`. Establish `hchart : CP.conj ∘ CP.chartInv 0 = CP.chartInv 0 ∘ cv`.

Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp, CP.chartInv, CP.conj_mk]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun j => ?_) k` and prove the remaining obligations.

Simplify using `[CP.conjVec_apply]`. Establish `h1` using `CP.chartVec_succAbove (0 : Fin (N + 1)) z j`. Establish `h2` using `CP.chartVec_succAbove (0 : Fin (N + 1)) (cv z) j`. Simplify using `only [Fin.succAbove_zero] at h1 h2`. Rewrite using `[CP.conjVec_apply, h1, h2]`.

Establish `hdens : ∀ z, CP.fsVolumeDensity (0 : Fin (N + 1)) (cv z) = CP.fsVolumeDensity 0 z`. Introduce `z`. Simplify using `only [CP.fsVolumeDensity_eq, normSqSum, cv, Complex.norm_conj]`. Establish `hmeas : Measurable fun z => ENNReal.ofReal (CP.fsVolumeDensity (0 : Fin (N + 1)) z)` using `ENNReal.measurable_ofReal.comp (CP.measurable_fsVolumeDensity 0)`. Establish `hmap : (CP.fsChartMeasure (N` using `N) 0).map cv = CP.fsChartMeasure 0 := by`.

Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hcv.measurable hs, CP.fsChartMeasure, withDensity_apply _ (hcv.measurable hs), withDensity_apply _ hs, ← hcv.setLIntegral_comp_preimage hs hmeas]`. Simplify using `only [hdens]`. Rewrite using `[CP.fsMeasure, Measure.map_map CP.continuous_conj.measurable (CP.measurable_chartInv 0), hchart, ← Measure.map_map (CP.measurable_chartInv 0) hcv.measurable, hmap]`.
-/
theorem FSConjInvariant.proof : FSConjInvariant.Statement := by
  intro N
  let cv : (Fin N → ℂ) → (Fin N → ℂ) := fun z k => starRingEnd ℂ (z k)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume :=
    LinearIsometryEquiv.measurePreserving Complex.conjLIE
  have hcv : MeasurePreserving cv volume volume := volume_preserving_pi fun _ => hc
  have hchart : CP.conj ∘ CP.chartInv 0 = CP.chartInv 0 ∘ cv := by
    funext z
    simp only [Function.comp, CP.chartInv, CP.conj_mk]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [CP.conjVec_apply]
    · have h1 := CP.chartVec_succAbove (0 : Fin (N + 1)) z j
      have h2 := CP.chartVec_succAbove (0 : Fin (N + 1)) (cv z) j
      simp only [Fin.succAbove_zero] at h1 h2
      rw [CP.conjVec_apply, h1, h2]
  have hdens : ∀ z, CP.fsVolumeDensity (0 : Fin (N + 1)) (cv z) = CP.fsVolumeDensity 0 z := by
    intro z
    simp only [CP.fsVolumeDensity_eq, normSqSum, cv, Complex.norm_conj]
  have hmeas : Measurable fun z => ENNReal.ofReal (CP.fsVolumeDensity (0 : Fin (N + 1)) z) :=
    ENNReal.measurable_ofReal.comp (CP.measurable_fsVolumeDensity 0)
  have hmap : (CP.fsChartMeasure (N := N) 0).map cv = CP.fsChartMeasure 0 := by
    ext s hs
    rw [Measure.map_apply hcv.measurable hs, CP.fsChartMeasure,
      withDensity_apply _ (hcv.measurable hs), withDensity_apply _ hs,
      ← hcv.setLIntegral_comp_preimage hs hmeas]
    simp only [hdens]
  rw [CP.fsMeasure, Measure.map_map CP.continuous_conj.measurable (CP.measurable_chartInv 0), hchart,
    ← Measure.map_map (CP.measurable_chartInv 0) hcv.measurable, hmap]

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
