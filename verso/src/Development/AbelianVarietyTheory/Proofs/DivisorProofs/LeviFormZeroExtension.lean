import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `e S i c r f g hg hgf hf z hz hzS w`. Use `set V : Set (Fin e → ℂ) := {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} with hVdef`. Establish `hVo : IsOpen V`. Establish `hV : V = Metric.ball c r ∩ ⋂ k ∈ S, {z : Fin e → ℂ | z k ≠ 0}`. Use extensionality with `x`.

Simplify using `[V]`. Rewrite using `[hV]`. Conclude with `isOpen_ball.inter (isOpen_biInter_finset fun k _ => isOpen_ne_fun (continuous_apply k) continuous_const)`. Establish `hzero : ∀ y ∈ V, y i ≠ 0 → levi g y w = 0`. Introduce `y hy hyi`.

Establish `hmem : V ∩ {x : Fin e → ℂ | x i ≠ 0} ∈ 𝓝 y` using `(hVo.inter (isOpen_ne_fun (continuous_apply i) continuous_const)).mem_nhds ⟨hy, hyi⟩`. Establish `hev : g =ᶠ[𝓝 y] f` using `by filter_upwards [hmem] with x hx using hgf x hx.1.1 hx.1.2 hx.2`. Rewrite using `[levi_congr hev]`. Conclude with `hf y hy.1 hy.2 hyi w`. Establish `hzV : z ∈ V` using `⟨hz, hzS⟩`.

Distinguish the cases in `hzi : z i ≠ 0`. Conclude with `hzero z hzV hzi`. Use `push_neg at hzi`. Establish `hg2 : ContDiffOn ℝ 2 g V` using `hg.of_le (by norm_cast)`. Establish `hcont : ContinuousOn (fun y => levi g y w) V`.

Establish `h1` using `continuousOn_levi hVo hg2`. Establish `hpr : ContinuousOn (fun y : Fin e → ℂ => ((y, w) : (Fin e → ℂ) × (Fin e → ℂ))) V` using `(continuous_id.prodMk continuous_const).continuousOn`. Establish `h3` using `ContinuousOn.comp (f := fun y : Fin e → ℂ => ((y, w) : (Fin e → ℂ) × (Fin e → ℂ))) h1 hpr (fun x hx => ⟨hx, Set.mem_univ _⟩)`. Conclude with `h3`. Use `set A : Set (Fin e → ℂ) := V ∩ {x | x i ≠ 0} with hAdef`.

Set `p : ℝ → (Fin e → ℂ)` to `fun t => z + (t : ℂ) • Pi.single i 1`. Establish `hp : Tendsto p (𝓝[≠] 0) (𝓝 z)`. Establish `hpc : Continuous p` using `by fun_prop`. Establish `h0` using `hpc.tendsto 0`. Establish `hp0 : p 0 = z` using `by simp [p]`.

Rewrite `h0` using `[hp0]`. Conclude with `h0.mono_left nhdsWithin_le_nhds`. Establish `hpA : ∀ᶠ t in 𝓝[≠] (0:ℝ), p t ∈ A`. Establish `h1 : ∀ᶠ t in 𝓝[≠] (0:ℝ), p t ∈ V` using `hp.eventually (hVo.mem_nhds hzV)`. Establish `h2 : ∀ᶠ t in 𝓝[≠] (0:ℝ), t ≠ 0` using `self_mem_nhdsWithin`.

Use `filter_upwards [h1, h2] with t ht1 ht2`. Use `⟨ht1, ?_⟩` and prove the remaining obligations. Simplify using `[p, hzi, ht2]`. Establish `hcl : z ∈ closure A` using `mem_closure_of_tendsto hp hpA`. Use `haveI : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl`.

Establish `hT : Tendsto (fun y => levi g y w) (𝓝[A] z) (𝓝 (levi g z w))` using `((hcont z hzV).mono inter_subset_left).tendsto`. Establish `hT0 : Tendsto (fun y => levi g y w) (𝓝[A] z) (𝓝 0)`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with y hy`. Conclude with `(hzero y hy.1 hy.2).symm`.

Conclude with `tendsto_nhds_unique hT hT0`.
-/
theorem levi_eq_zero_of_eq_off_coord_hyperplane :
    ∀ (e : ℕ) (S : Finset (Fin e)) (i : Fin e) (c : Fin e → ℂ) (r : ℝ) (f g : (Fin e → ℂ) → ℝ), ContDiffOn ℝ ∞ g {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} → (∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → g z = f z) → (∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → z i ≠ 0 → ∀ w, levi f z w = 0) → ∀ z ∈ Metric.ball c r, (∀ k ∈ S, z k ≠ 0) → ∀ w, levi g z w = 0 := by
  intro e S i c r f g hg hgf hf z hz hzS w
  set V : Set (Fin e → ℂ) := {z | z ∈ Metric.ball c r ∧ ∀ k ∈ S, z k ≠ 0} with hVdef
  have hVo : IsOpen V := by
    have hV : V = Metric.ball c r ∩ ⋂ k ∈ S, {z : Fin e → ℂ | z k ≠ 0} := by
      ext x; simp [V]
    rw [hV]
    exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
      isOpen_ne_fun (continuous_apply k) continuous_const)
  have hzero : ∀ y ∈ V, y i ≠ 0 → levi g y w = 0 := by
    intro y hy hyi
    have hmem : V ∩ {x : Fin e → ℂ | x i ≠ 0} ∈ 𝓝 y :=
      (hVo.inter (isOpen_ne_fun (continuous_apply i) continuous_const)).mem_nhds ⟨hy, hyi⟩
    have hev : g =ᶠ[𝓝 y] f := by
      filter_upwards [hmem] with x hx using hgf x hx.1.1 hx.1.2 hx.2
    rw [levi_congr hev]
    exact hf y hy.1 hy.2 hyi w
  have hzV : z ∈ V := ⟨hz, hzS⟩
  by_cases hzi : z i ≠ 0
  · exact hzero z hzV hzi
  push_neg at hzi
  have hg2 : ContDiffOn ℝ 2 g V := hg.of_le (by norm_cast)
  have hcont : ContinuousOn (fun y => levi g y w) V := by
    have h1 := continuousOn_levi hVo hg2
    have hpr : ContinuousOn (fun y : Fin e → ℂ => ((y, w) : (Fin e → ℂ) × (Fin e → ℂ))) V :=
      (continuous_id.prodMk continuous_const).continuousOn
    have h3 := ContinuousOn.comp (f := fun y : Fin e → ℂ => ((y, w) : (Fin e → ℂ) × (Fin e → ℂ)))
      h1 hpr (fun x hx => ⟨hx, Set.mem_univ _⟩)
    exact h3
  set A : Set (Fin e → ℂ) := V ∩ {x | x i ≠ 0} with hAdef
  let p : ℝ → (Fin e → ℂ) := fun t => z + (t : ℂ) • Pi.single i 1
  have hp : Tendsto p (𝓝[≠] 0) (𝓝 z) := by
    have hpc : Continuous p := by fun_prop
    have h0 := hpc.tendsto 0
    have hp0 : p 0 = z := by simp [p]
    rw [hp0] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hpA : ∀ᶠ t in 𝓝[≠] (0:ℝ), p t ∈ A := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0:ℝ), p t ∈ V := hp.eventually (hVo.mem_nhds hzV)
    have h2 : ∀ᶠ t in 𝓝[≠] (0:ℝ), t ≠ 0 := self_mem_nhdsWithin
    filter_upwards [h1, h2] with t ht1 ht2
    refine ⟨ht1, ?_⟩
    simp [p, hzi, ht2]
  have hcl : z ∈ closure A := mem_closure_of_tendsto hp hpA
  haveI : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hT : Tendsto (fun y => levi g y w) (𝓝[A] z) (𝓝 (levi g z w)) :=
    ((hcont z hzV).mono inter_subset_left).tendsto
  have hT0 : Tendsto (fun y => levi g y w) (𝓝[A] z) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hzero y hy.1 hy.2).symm
  exact tendsto_nhds_unique hT hT0

end GlobalTheory
