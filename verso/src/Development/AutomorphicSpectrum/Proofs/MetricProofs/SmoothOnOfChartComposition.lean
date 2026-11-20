import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

/- English proof (translation)
Introduce `j y hy`. Take `⟨hyt, hys, hyO⟩` from `hy`. Establish `han : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y` using `(hψ j).1 y ⟨hyt, hys⟩`. Establish `hτ : ContDiffAt ℝ ∞ (ψ ∘ (A.chart j).symm) y` using `(han.restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top`. Establish `hGat : ContDiffAt ℝ ∞ G ((ψ ∘ (A.chart j).symm) y)` using `hG.contDiffAt (hO.mem_nhds hyO)`.

Conclude with `(hGat.comp y hτ).contDiffWithinAt`.
-/
theorem smoothOn_comp_compatChart (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ)
    (hψ : IsCompatChart A ψ) (hO : IsOpen O) (_hOt : O ⊆ ψ.target)
    (hG : ContDiffOn ℝ ∞ G O) : A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  intro j y hy
  obtain ⟨hyt, hys, hyO⟩ := hy
  have han : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hys⟩
  have hτ : ContDiffAt ℝ ∞ (ψ ∘ (A.chart j).symm) y :=
    (han.restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
  have hGat : ContDiffAt ℝ ∞ G ((ψ ∘ (A.chart j).symm) y) :=
    hG.contDiffAt (hO.mem_nhds hyO)
  exact (hGat.comp y hτ).contDiffWithinAt

/- English proof (translation)
Introduce `e X _ A ψ O G h1 h2 h3 h4` and use `smoothOn_comp_compatChart e X A ψ O G h1 h2 h3 h4`.
-/
theorem smoothOn_comp_compatChart' : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) :=
  fun e X _ A ψ O G h1 h2 h3 h4 => smoothOn_comp_compatChart e X A ψ O G h1 h2 h3 h4

end GlobalTheory.CompanionTheory.Metric
