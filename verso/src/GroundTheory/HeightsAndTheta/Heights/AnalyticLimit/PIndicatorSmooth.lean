import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open Filter Topology
open scoped ContDiff

/- English proof (translation)
Introduce `X _ D A U O χ h hU hO hχ hsupp hh j`. Use `set φ := A.chart j`. Use `fun v hv => (?_ : ContDiffAt ℝ ∞ _ v).contDiffWithinAt` and prove the remaining obligations. Distinguish the cases in `hx : φ.symm v ∈ O`. Establish `hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (U ∩ O))` using `φ.isOpen_inter_preimage_symm (hU.inter hO)`.

Establish `hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ O)` using `⟨hv.1, hv.2, hx⟩`. Establish `hχT : ContDiffOn ℝ ∞ (χ ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (U ∩ O))` using `(hχ j).mono fun z hz => ⟨hz.1, Set.mem_univ _⟩`. Establish `hprod : ContDiffOn ℝ ∞ (fun z => (χ ∘ φ.symm) z * (h ∘ φ.symm) z) (φ.target ∩ φ.symm ⁻¹' (U ∩ O))` using `hχT.mul (hh j)`. Use `(hprod.contDiffAt (hT.mem_nhds hvT)).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hT.mem_nhds hvT] with z hz`.

Simplify using `[Function.comp, Set.indicator_of_mem hz.2.2]`. Establish `hns : φ.symm v ∉ tsupport χ` using `fun hm => hx (hsupp hm)`. Establish `hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ)` using `φ.isOpen_inter_preimage_symm (isClosed_tsupport χ).isOpen_compl`. Establish `hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ` using `⟨hv.1, hns⟩`. Use `(contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hT.mem_nhds hvT] with z hz`. Establish `h0 : χ (φ.symm z) = 0` using `image_eq_zero_of_notMem_tsupport hz.2`. Distinguish the cases in `hzO : φ.symm z ∈ O`. Simplify using `[Function.comp, Set.indicator_of_mem hzO, h0]`. Simplify using `[Function.comp, Set.indicator_of_notMem hzO]`.
-/
theorem IndicatorSmooth.proof : IndicatorSmooth.Statement := by
  intro X _ D A U O χ h hU hO hχ hsupp hh j
  set φ := A.chart j
  refine fun v hv => (?_ : ContDiffAt ℝ ∞ _ v).contDiffWithinAt
  by_cases hx : φ.symm v ∈ O
  ·
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := φ.isOpen_inter_preimage_symm (hU.inter hO)
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ O) := ⟨hv.1, hv.2, hx⟩
    have hχT : ContDiffOn ℝ ∞ (χ ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) :=
      (hχ j).mono fun z hz => ⟨hz.1, Set.mem_univ _⟩
    have hprod : ContDiffOn ℝ ∞ (fun z => (χ ∘ φ.symm) z * (h ∘ φ.symm) z)
        (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := hχT.mul (hh j)
    refine (hprod.contDiffAt (hT.mem_nhds hvT)).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    simp [Function.comp, Set.indicator_of_mem hz.2.2]
  ·
    have hns : φ.symm v ∉ tsupport χ := fun hm => hx (hsupp hm)
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ) :=
      φ.isOpen_inter_preimage_symm (isClosed_tsupport χ).isOpen_compl
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ := ⟨hv.1, hns⟩
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    have h0 : χ (φ.symm z) = 0 := image_eq_zero_of_notMem_tsupport hz.2
    by_cases hzO : φ.symm z ∈ O
    · simp [Function.comp, Set.indicator_of_mem hzO, h0]
    · simp [Function.comp, Set.indicator_of_notMem hzO]

end GroundTheory.Heights₂.Heights.AnalyticLimit
