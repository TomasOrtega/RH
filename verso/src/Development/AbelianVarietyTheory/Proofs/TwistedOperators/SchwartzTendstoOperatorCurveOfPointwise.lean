import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open Filter Topology
open scoped Uniformity

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ S hS g g₀ hg`. Use `haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V`. Rewrite using `[tendsto_iff_seq_tendsto]`. Introduce `u hu`. Establish `hq` using `schwartz_withSeminorms ℂ V ℂ`.

Establish `hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n))`. Use `hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_` and prove the remaining obligations. Introduce `k f`. Conclude with `((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range`. Establish `hE` using `hUE.equicontinuous g₀`.

Establish `h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ))`. Introduce `U hU`. Use `(hg.comp hu).eventually (hE U hU)` as an intermediate fact. Rewrite using `[Filter.mem_map]`. Conclude with `this.mono fun n hn => hn n`.

Conclude with `((hS g₀).comp hu).congr_uniformity h1`.
-/
theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
