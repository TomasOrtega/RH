import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

/- English proof (translation)
Introduce `e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w`. Establish `hp : (B.chart j).symm y ∈ (B.chart j).source` using `(B.chart j).map_target hy.1`. Take `⟨k, hk⟩` from `A.cover ((B.chart j).symm y)`. Establish `hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y` using `hAB.2 j k y ⟨hy.1, hk⟩`. Establish `hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y` using `(A.chart k).left_inv hk`.

Establish `htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target` using `(A.chart k).map_source hk`. Establish `hthU : (B.chart j).symm y ∈ th.U x₀` using `hsrc hp`. Establish `hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀)` using `(A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)`. Establish `hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U)` using `(A.chart k).isOpen_inter_preimage_symm hU`. Establish `hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀` using `⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩`.

Establish `hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U` using `⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩`. Establish `h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞` using `WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)`. Establish `hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y)` using `((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2`. Establish `hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y)` using `((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2`. Establish `hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ((A.chart k ∘ (B.chart j).symm) y)` using `hC1.add hC2`.

Establish `hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y] ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘ (A.chart k ∘ (B.chart j).symm))`. Establish `h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source` using `((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)`. Use `filter_upwards [h1] with z hz`. Simplify using `only [Function.comp_apply, (A.chart k).left_inv hz]`. Rewrite using `[levi_congr hev w, levi_comp w hτ hC]`.

Conclude with `hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _`.
-/
theorem levi_nonneg_of_compat_fixedBase : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B →
    IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) →
    (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    ∀ w : Fin e → ℂ,
    0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  intro e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w
  have hp : (B.chart j).symm y ∈ (B.chart j).source := (B.chart j).map_target hy.1
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y := hAB.2 j k y ⟨hy.1, hk⟩
  have hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y :=
    (A.chart k).left_inv hk
  have htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target := (A.chart k).map_source hk
  have hthU : (B.chart j).symm y ∈ th.U x₀ := hsrc hp
  have hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀) :=
    (A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)
  have hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀ :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩
  have hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2
  have hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2
  have hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z))
      ((A.chart k ∘ (B.chart j).symm) y) := hC1.add hC2
  have hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y]
      ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘
        (A.chart k ∘ (B.chart j).symm)) := by
    have h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source :=
      ((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  rw [levi_congr hev w, levi_comp w hτ hC]
  exact hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _

end GlobalTheory.CompanionTheory.LeviChart
