import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

/- English proof (translation)
Establish `hS : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(A.chart i).isOpen_inter_preimage_symm hE.isOpen`. Establish `hmem : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U` using `⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩`. Rewrite using `[contDiffAt_euclidean]`. Introduce `k`. Establish `hk : DifferentiableOn ℂ (fun w => (z ∘ (A.chart i).symm) w k) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(EuclideanSpace.proj (𝕜 := ℂ) k).differentiable.comp_differentiableOn (hE.holo i)`.

Conclude with `(contDiffOn_of_differentiableOn n _ _ hS hk).contDiffAt (hS.mem_nhds hmem)`.
-/
theorem Etale.contDiffAt_chart {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n} (hE : Etale A U z) {x : Y} (hx : x ∈ U)
    {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have hS : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hmem : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  rw [contDiffAt_euclidean]
  intro k
  have hk : DifferentiableOn ℂ (fun w => (z ∘ (A.chart i).symm) w k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable.comp_differentiableOn (hE.holo i)
  exact (contDiffOn_of_differentiableOn n _ _ hS hk).contDiffAt (hS.mem_nhds hmem)

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A U z hE e he v hv i hi`. Use `set g : V n → V n := z ∘ (A.chart i).symm with hg_def`. Establish `hg : ContDiffAt ℂ ∞ g (A.chart i (e.symm v : U))` using `hE.contDiffAt_chart (e.symm v).2 hi`. Establish `hdet : (jz A z i (e.symm v : U)).det ≠ 0` using `hE.det_ne i _ (e.symm v).2 hi`. Use `set f' : V n ≃L[ℂ] V n := (jz A z i (e.symm v : U)).toContinuousLinearEquivOfDetNeZero hdet with hf'_def`.

Establish `hf'coe : (f' : V n →L[ℂ] V n) = fderiv ℂ g (A.chart i (e.symm v : U))`. Use extensionality with `w`. Both sides reduce to the same expression. Establish `hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) (A.chart i (e.symm v : U))`. Rewrite using `[hf'coe]; exact (hg.differentiableAt (by simp)).hasFDerivAt`.

Establish `hn : (∞ : WithTop ℕ∞) ≠ 0` using `by simp`. Establish `hstrict` using `hg.hasStrictFDerivAt' hf' hn`. Establish `hgv : g (A.chart i (e.symm v : U)) = v`. Establish `h1 : z (e.symm v : U) = e (e.symm v)` using `he (e.map_target hv)`. Use `show z ((A.chart i).symm (A.chart i (e.symm v : U))) = v`.

Rewrite using `[(A.chart i).left_inv hi, h1, e.right_inv hv]`. Use `set h : V n → V n := fun v' => A.chart i (e.symm v' : U) with hh_def`. Establish `hcoe : ContinuousAt (fun v' => ((e.symm v' : U) : Y)) v` using `continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)`. Establish `hhc : ContinuousAt h v` using `ContinuousAt.comp (g := A.chart i) (f := fun v' => ((e.symm v' : U) : Y)) (x := v) ((A.chart i).continuousAt hi) hcoe`. Establish `hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source` using `hcoe.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)`.

Establish `htgt : ∀ᶠ v' in 𝓝 v, v' ∈ e.target` using `e.open_target.mem_nhds hv`. Establish `hright : ∀ᶠ v' in 𝓝 v, g (h v') = v'` using `by filter_upwards [hsrc, htgt] with v' h1 h2`. Establish `h3 : z (e.symm v') = e (e.symm v')` using `he (e.map_target h2)`. Use `show z ((A.chart i).symm (A.chart i (e.symm v' : U))) = v'`. Rewrite using `[(A.chart i).left_inv h1, h3, e.right_inv h2]`.

Establish `hleft : ∀ᶠ v' in 𝓝 v, hstrict.localInverse g f' (A.chart i (e.symm v : U)) (g (h v')) = h v'` using `hhc.tendsto.eventually hstrict.eventually_left_inverse`. Establish `heq : h =ᶠ[𝓝 v] hstrict.localInverse g f' (A.chart i (e.symm v : U))` using `by filter_upwards [hleft, hright] with v' h1 h2`. Rewrite using `[← h1, h2]`. Establish `hinv` using `hstrict.to_localInverse`. Rewrite `hinv` using `[hgv]`.

Establish `hGc : ContDiffAt ℂ ∞ (hstrict.localInverse g f' (A.chart i (e.symm v : U))) v`. Use `hg.to_localInverse hf' hn` as an intermediate fact. Rewrite `this` using `[hgv]`. Conclude with `this`. Use `⟨hGc.congr_of_eventuallyEq heq, hsrc, fun ξ => ?_⟩` and prove the remaining obligations.

Establish `hfd : fderiv ℂ h v = (f'.symm : V n →L[ℂ] V n)` using `heq.fderiv_eq.trans hinv.hasFDerivAt.fderiv`. Express the relevant statement in the definitionally equal form `fderiv ℂ h v (jz A z i (e.symm v : U) ξ) = ξ`. Rewrite using `[hfd]`. Conclude with `f'.symm_apply_apply ξ`.
-/
theorem etale_local_inverse : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → ∀ v ∈ e.target, ∀ i, ((e.symm v : U) : Y) ∈ (A.chart i).source → ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : U)) v ∧ (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) ∧ ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : U)) v (jz A z i (e.symm v : U) ξ) = ξ := by
  intro n Y _ _ _ _ _ ι La _ A U z hE e he v hv i hi
  set g : V n → V n := z ∘ (A.chart i).symm with hg_def
  have hg : ContDiffAt ℂ ∞ g (A.chart i (e.symm v : U)) := hE.contDiffAt_chart (e.symm v).2 hi
  have hdet : (jz A z i (e.symm v : U)).det ≠ 0 := hE.det_ne i _ (e.symm v).2 hi
  set f' : V n ≃L[ℂ] V n :=
    (jz A z i (e.symm v : U)).toContinuousLinearEquivOfDetNeZero hdet with hf'_def
  have hf'coe : (f' : V n →L[ℂ] V n) = fderiv ℂ g (A.chart i (e.symm v : U)) := by
    ext w; rfl
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) (A.chart i (e.symm v : U)) := by
    rw [hf'coe]; exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hg.hasStrictFDerivAt' hf' hn

  have hgv : g (A.chart i (e.symm v : U)) = v := by
    have h1 : z (e.symm v : U) = e (e.symm v) := he (e.map_target hv)
    show z ((A.chart i).symm (A.chart i (e.symm v : U))) = v
    rw [(A.chart i).left_inv hi, h1, e.right_inv hv]

  set h : V n → V n := fun v' => A.chart i (e.symm v' : U) with hh_def
  have hcoe : ContinuousAt (fun v' => ((e.symm v' : U) : Y)) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hhc : ContinuousAt h v :=
    ContinuousAt.comp (g := A.chart i) (f := fun v' => ((e.symm v' : U) : Y)) (x := v)
      ((A.chart i).continuousAt hi) hcoe
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hcoe.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)
  have htgt : ∀ᶠ v' in 𝓝 v, v' ∈ e.target := e.open_target.mem_nhds hv

  have hright : ∀ᶠ v' in 𝓝 v, g (h v') = v' := by
    filter_upwards [hsrc, htgt] with v' h1 h2
    have h3 : z (e.symm v') = e (e.symm v') := he (e.map_target h2)
    show z ((A.chart i).symm (A.chart i (e.symm v' : U))) = v'
    rw [(A.chart i).left_inv h1, h3, e.right_inv h2]

  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse g f' (A.chart i (e.symm v : U)) (g (h v')) = h v' :=
    hhc.tendsto.eventually hstrict.eventually_left_inverse
  have heq : h =ᶠ[𝓝 v] hstrict.localInverse g f' (A.chart i (e.symm v : U)) := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hinv := hstrict.to_localInverse
  rw [hgv] at hinv
  have hGc : ContDiffAt ℂ ∞ (hstrict.localInverse g f' (A.chart i (e.symm v : U))) v := by
    have := hg.to_localInverse hf' hn
    rw [hgv] at this
    exact this
  refine ⟨hGc.congr_of_eventuallyEq heq, hsrc, fun ξ => ?_⟩
  have hfd : fderiv ℂ h v = (f'.symm : V n →L[ℂ] V n) :=
    heq.fderiv_eq.trans hinv.hasFDerivAt.fderiv
  change fderiv ℂ h v (jz A z i (e.symm v : U) ξ) = ξ
  rw [hfd]
  exact f'.symm_apply_apply ξ

end GlobalTheory.OTY
