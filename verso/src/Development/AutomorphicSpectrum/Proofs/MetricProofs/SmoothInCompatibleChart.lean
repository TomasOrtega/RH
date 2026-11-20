import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

/- English proof (translation)
Introduce `e X _ A ψ U g hψ hU hg z hz hzU`. Take `⟨j, hj⟩` from `A.cover (ψ.symm z)`. Establish `hτ : ContDiffAt ℝ ∞ (⇑(A.chart j) ∘ ⇑ψ.symm) z` using `(((hψ j).2 z ⟨hz, hj⟩).contDiffAt).restrict_scalars ℝ`. Establish `hy : (A.chart j) (ψ.symm z) ∈ (A.chart j).target ∩ ⇑(A.chart j).symm ⁻¹' U`. Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations.

Use `show (A.chart j).symm ((A.chart j) (ψ.symm z)) ∈ U`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `hzU`. Establish `hgc : ContDiffAt ℝ ∞ (g ∘ ⇑(A.chart j).symm) ((A.chart j) (ψ.symm z))` using `(hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hy)`. Establish `hcomp` using `hgc.comp z hτ`.

Apply `hcomp.congr_of_eventuallyEq` to reduce the goal to its premises. Establish `hev : ∀ᶠ w in 𝓝 z, ψ.symm w ∈ (A.chart j).source` using `(ψ.continuousAt_symm hz).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)`. Use `filter_upwards [hev] with w hw`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hw]`.
-/
theorem contDiffAt_comp_compatChart_symm :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
      (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ),
      IsCompatChart A ψ → IsOpen U → A.SmoothOn U g →
        ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  intro e X _ A ψ U g hψ hU hg z hz hzU
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hτ : ContDiffAt ℝ ∞ (⇑(A.chart j) ∘ ⇑ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt).restrict_scalars ℝ
  have hy : (A.chart j) (ψ.symm z) ∈ (A.chart j).target ∩ ⇑(A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ.symm z)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hzU
  have hgc : ContDiffAt ℝ ∞ (g ∘ ⇑(A.chart j).symm) ((A.chart j) (ψ.symm z)) :=
    (hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hcomp := hgc.comp z hτ
  apply hcomp.congr_of_eventuallyEq
  have hev : ∀ᶠ w in 𝓝 z, ψ.symm w ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]

end GlobalTheory.CompanionTheory.Metric
