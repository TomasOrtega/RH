import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord

/- English proof (translation)
Introduce `e n X Y _ _ A B pr hloc`. Establish `key : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ pr x' = (B.chart kb).symm (fun i => ψ x' (σ i)) ∧ (fun i => ψ x' (σ i)) ∈ (B.chart kb).target`. Introduce `x`. Take `⟨ψ, kb, σ, hψ, hx, h⟩` from `hloc x`. Use `⟨ψ, kb, σ, hψ, hx, fun x' hx' => ?_⟩` and prove the remaining obligations.

Take `⟨hs, hc⟩` from `h x' hx'`. Establish `hfun : (fun i => ψ x' (σ i)) = B.chart kb (pr x')` using `funext fun i => (hc i).symm`. Use `⟨hs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun, (B.chart kb).left_inv hs]`. Rewrite using `[hfun]`.

Conclude with `(B.chart kb).map_source hs`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨ψ, kb, σ, -, hx, h⟩` from `key x`. Set `L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)`.

Establish `hcont : ContinuousOn ((B.chart kb).symm ∘ L ∘ ψ) ψ.source` using `(B.chart kb).continuousOn_symm.comp (L.continuous.comp_continuousOn ψ.continuousOn) (fun x' hx' => (h x' hx').2.2)`. Establish `heq : ((B.chart kb).symm ∘ L ∘ ψ) =ᶠ[𝓝 x] pr` using `Filter.eventually_of_mem (ψ.open_source.mem_nhds hx) fun x' hx' => ((h x' hx').2.1).symm`. Conclude with `(hcont.continuousAt (ψ.open_source.mem_nhds hx)).congr heq`. Introduce `j k y hy`. Take `⟨hyt, hys⟩` from `hy`.

Take `⟨ψ, kb, σ, hψ, hx, h⟩` from `key ((A.chart j).symm y)`. Set `L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)`. Establish `h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y` using `(hψ j).1 y ⟨hyt, hx⟩`. Establish `h2 : AnalyticAt ℂ (B.chart k ∘ (B.chart kb).symm) (L (ψ ((A.chart j).symm y)))`. Apply `B.holo kb k` to reduce the goal to its premises.

Use `⟨(h _ hx).2.2, ?_⟩` and prove the remaining obligations. Use `show (B.chart kb).symm (fun i => ψ ((A.chart j).symm y) (σ i)) ∈ (B.chart k).source`. Rewrite using `[← (h _ hx).2.1]`. Conclude with `hys`. Establish `h3 : AnalyticAt ℂ ((B.chart k ∘ (B.chart kb).symm) ∘ L ∘ (ψ ∘ (A.chart j).symm)) y` using `AnalyticAt.comp (f := L ∘ (ψ ∘ (A.chart j).symm)) h2 (AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) (L.analyticAt _) h1)`.

Apply `h3.congr` to reduce the goal to its premises. Establish `hnb : ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ ψ.source` using `(A.chart j).continuousAt_symm hyt (ψ.open_source.mem_nhds hx)`. Use `filter_upwards [hnb] with y' hy'`. Simplify using `only [Function.comp_apply]`. Rewrite using `[(h _ hy').2.1]`.

Both sides reduce to the same expression.
-/
theorem holoMap_of_coord : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  intro e n X Y _ _ A B pr hloc
  have key : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧
        pr x' = (B.chart kb).symm (fun i => ψ x' (σ i)) ∧ (fun i => ψ x' (σ i)) ∈ (B.chart kb).target := by
    intro x
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := hloc x
    refine ⟨ψ, kb, σ, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨hs, hc⟩ := h x' hx'
    have hfun : (fun i => ψ x' (σ i)) = B.chart kb (pr x') := funext fun i => (hc i).symm
    refine ⟨hs, ?_, ?_⟩
    · rw [hfun, (B.chart kb).left_inv hs]
    · rw [hfun]
      exact (B.chart kb).map_source hs
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ψ, kb, σ, -, hx, h⟩ := key x
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have hcont : ContinuousOn ((B.chart kb).symm ∘ L ∘ ψ) ψ.source :=
      (B.chart kb).continuousOn_symm.comp (L.continuous.comp_continuousOn ψ.continuousOn)
        (fun x' hx' => (h x' hx').2.2)
    have heq : ((B.chart kb).symm ∘ L ∘ ψ) =ᶠ[𝓝 x] pr :=
      Filter.eventually_of_mem (ψ.open_source.mem_nhds hx) fun x' hx' => ((h x' hx').2.1).symm
    exact (hcont.continuousAt (ψ.open_source.mem_nhds hx)).congr heq
  · intro j k y hy
    obtain ⟨hyt, hys⟩ := hy
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := key ((A.chart j).symm y)
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hx⟩
    have h2 : AnalyticAt ℂ (B.chart k ∘ (B.chart kb).symm) (L (ψ ((A.chart j).symm y))) := by
      apply B.holo kb k
      refine ⟨(h _ hx).2.2, ?_⟩
      show (B.chart kb).symm (fun i => ψ ((A.chart j).symm y) (σ i)) ∈ (B.chart k).source
      rw [← (h _ hx).2.1]
      exact hys
    have h3 : AnalyticAt ℂ ((B.chart k ∘ (B.chart kb).symm) ∘ L ∘ (ψ ∘ (A.chart j).symm)) y :=
      AnalyticAt.comp (f := L ∘ (ψ ∘ (A.chart j).symm)) h2
        (AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) (L.analyticAt _) h1)
    apply h3.congr
    have hnb : ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ ψ.source :=
      (A.chart j).continuousAt_symm hyt (ψ.open_source.mem_nhds hx)
    filter_upwards [hnb] with y' hy'
    simp only [Function.comp_apply]
    rw [(h _ hy').2.1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord
