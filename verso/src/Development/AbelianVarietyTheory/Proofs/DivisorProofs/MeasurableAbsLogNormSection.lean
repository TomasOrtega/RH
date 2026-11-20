import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.AbsLogNormMeas

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `y0`. Establish `hloc : ∀ y ∈ L.U y0, ContinuousAt (fun z => ‖s y0 z‖ * Real.exp (-L.φ y0 z)) y`. Introduce `y hy`. Take `⟨j, hj⟩` from `A.cover y`.

Use `set c := A.chart j`. Establish `hopen : IsOpen (c.target ∩ c.symm ⁻¹' L.U y0)` using `c.continuousOn_symm.isOpen_inter_preimage c.open_target (L.isOpen_U y0)`. Establish `hmem : c y ∈ c.target ∩ c.symm ⁻¹' L.U y0`. Use `⟨c.map_source hj, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, c.left_inv hj]`.

Conclude with `hy`. Establish `hg : ContinuousAt (fun w => ‖s y0 (c.symm w)‖ * Real.exp (-L.φ y0 (c.symm w))) (c y)`. Establish `h1 : ContinuousAt (s y0 ∘ c.symm) (c y)` using `((hs.1 y0 j) (c y) hmem).continuousAt`. Establish `h2 : ContinuousAt (L.φ y0 ∘ c.symm) (c y)` using `((hL.1 y0 j).continuousOn).continuousAt (hopen.mem_nhds hmem)`. Conclude with `(h1.norm).mul (h2.neg.rexp)`.

Establish `hc : ContinuousAt c y` using `c.continuousAt hj`. Establish `hcomp` using `hg.comp (f := c) (x := y) (by simpa using hc)`. Use `hcomp.congr ?_` and prove the remaining obligations. Use `filter_upwards [c.open_source.mem_nhds hj] with z hz`. Simplify using `[Function.comp, c.left_inv hz]`.

Use `(hloc y0 (L.mem_U y0)).congr ?_` and prove the remaining obligations. Use `filter_upwards [(L.isOpen_U y0).mem_nhds (L.mem_U y0)] with y hy`. Use `hs.2 y y0 y ⟨L.mem_U y, hy⟩` as an intermediate fact. Simplify using `only [normSec]`. Conclude with `this.symm`.
-/
theorem continuous_normSec {d : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas d X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous (normSec L s) := by
  rw [continuous_iff_continuousAt]
  intro y0

  have hloc : ∀ y ∈ L.U y0, ContinuousAt (fun z => ‖s y0 z‖ * Real.exp (-L.φ y0 z)) y := by
    intro y hy
    obtain ⟨j, hj⟩ := A.cover y
    set c := A.chart j
    have hopen : IsOpen (c.target ∩ c.symm ⁻¹' L.U y0) :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target (L.isOpen_U y0)
    have hmem : c y ∈ c.target ∩ c.symm ⁻¹' L.U y0 := by
      refine ⟨c.map_source hj, ?_⟩
      simp only [Set.mem_preimage, c.left_inv hj]; exact hy
    have hg : ContinuousAt (fun w => ‖s y0 (c.symm w)‖ * Real.exp (-L.φ y0 (c.symm w))) (c y) := by
      have h1 : ContinuousAt (s y0 ∘ c.symm) (c y) := ((hs.1 y0 j) (c y) hmem).continuousAt
      have h2 : ContinuousAt (L.φ y0 ∘ c.symm) (c y) :=
        ((hL.1 y0 j).continuousOn).continuousAt (hopen.mem_nhds hmem)
      exact (h1.norm).mul (h2.neg.rexp)
    have hc : ContinuousAt c y := c.continuousAt hj
    have hcomp := hg.comp (f := c) (x := y) (by simpa using hc)
    refine hcomp.congr ?_
    filter_upwards [c.open_source.mem_nhds hj] with z hz
    simp [Function.comp, c.left_inv hz]
  refine (hloc y0 (L.mem_U y0)).congr ?_
  filter_upwards [(L.isOpen_U y0).mem_nhds (L.mem_U y0)] with y hy
  have := hs.2 y y0 y ⟨L.mem_U y, hy⟩
  simp only [normSec]
  exact this.symm

/- English proof (translation)
Introduce `d X _ A L s hL hs Y _ _ _ μ hμ`. Set `F : ℝ → ℝ≥0∞` to `fun t => if t = 0 then ∞ else ENNReal.ofReal |Real.log t|`. Establish `hF : Measurable F` using `Measurable.ite (measurableSet_singleton 0) measurable_const (ENNReal.measurable_ofReal.comp (Real.measurable_log.abs))`. Establish `hN : Measurable fun y => normSec L s (μ y)` using `((continuous_normSec A L s hL hs).comp hμ).measurable`. Establish `heq : (fun y => absLogNorm L s (μ y)) = F ∘ fun y => normSec L s (μ y)`.

Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp, F, absLogNorm, normSec, logNormSec]`. Establish `he : Real.exp (-L.φ (μ y) (μ y)) ≠ 0` using `(Real.exp_pos _).ne'`. Distinguish the cases in `h0 : s (μ y) (μ y) = 0`. Simplify using `[h0]`.

Simplify using `[h0, he]`. Rewrite using `[heq]`. Conclude with `hF.comp hN`.
-/
theorem measurable_absLogNorm_comp : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ),
    IsPotential A L → IsSection A L s → ∀ (Y : Type) [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (μ : Y → X), Continuous μ → Measurable fun y => absLogNorm L s (μ y) := by
  intro d X _ A L s hL hs Y _ _ _ μ hμ
  classical
  let F : ℝ → ℝ≥0∞ := fun t => if t = 0 then ∞ else ENNReal.ofReal |Real.log t|
  have hF : Measurable F :=
    Measurable.ite (measurableSet_singleton 0) measurable_const
      (ENNReal.measurable_ofReal.comp (Real.measurable_log.abs))
  have hN : Measurable fun y => normSec L s (μ y) :=
    ((continuous_normSec A L s hL hs).comp hμ).measurable
  have heq : (fun y => absLogNorm L s (μ y)) = F ∘ fun y => normSec L s (μ y) := by
    funext y
    simp only [Function.comp, F, absLogNorm, normSec, logNormSec]
    have he : Real.exp (-L.φ (μ y) (μ y)) ≠ 0 := (Real.exp_pos _).ne'
    by_cases h0 : s (μ y) (μ y) = 0
    · simp [h0]
    · simp [h0, he]
  rw [heq]
  exact hF.comp hN

end GlobalTheory.AbsLogNormMeas
