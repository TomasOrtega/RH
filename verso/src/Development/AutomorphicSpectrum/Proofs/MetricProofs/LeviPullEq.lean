import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PshPull

open scoped ContDiff

/- English proof (translation)
Establish `h2 : (2 : WithTop ℕ∞) ≤ ∞` using `WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)`. Take `⟨p, hp⟩ : ∃ p, p = (A.chart j).symm y` from `⟨_, rfl⟩`. Rewrite `hyU`, the goal using `[← hp]`. Take `⟨j', hj'⟩` from `A'.cover (h p)`. Take `⟨W₁, hW₁o, hpW₁, G₁, hG₁, hE₁⟩` from `hth.2 x p p ⟨hyU, th.mem_U p⟩`.

Take `⟨W₂, hW₂o, hpW₂, G₂, hG₂, hE₂⟩` from `hs p (Set.mem_univ p)`. Establish `hτ : AnalyticAt ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y` using `hh.2 j j' y ⟨hy, by simpa [← hp] using hj'⟩`. Establish `hGa : AnalyticAt ℂ (fun t => G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)) y` using `AnalyticAt.add (hG₁ j y ⟨hy, by simpa [← hp] using hpW₁⟩) (hG₂ j y ⟨hy, by simpa [← hp] using hpW₂⟩)`. Establish `hτy : (A'.chart j' ∘ h ∘ (A.chart j).symm) y = A'.chart j' (h p)` using `by simp [← hp]`. Establish `hy' : A'.chart j' (h p) ∈ (A'.chart j').target` using `(A'.chart j').map_source hj'`.

Establish `hsy' : (A'.chart j').symm (A'.chart j' (h p)) = h p` using `(A'.chart j').left_inv hj'`. Establish `hψ₁ : ContDiffAt ℝ 2 (th'.φ (h p) ∘ (A'.chart j').symm) (A'.chart j' (h p))`. Establish `hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p))` using `(A'.chart j').isOpen_inter_preimage_symm (th'.isOpen_U _)`. Establish `hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p)` using `⟨hy', by simpa [hsy'] using th'.mem_U (h p)⟩`. Conclude with `(((hth'.1 (h p) j').contDiffAt (hO.mem_nhds hm))).of_le h2`.

Establish `hψ₂ : ContDiffAt ℝ 2 (u ∘ (A'.chart j').symm) (A'.chart j' (h p))`. Establish `hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ)`. Simplify using `using (A'.chart j').open_target`. Establish `hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ` using `⟨hy', Set.mem_univ _⟩`. Conclude with `((hu j').contDiffAt (hO.mem_nhds hm)).of_le h2`.

Establish `hψ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) (A'.chart j' (h p))` using `contDiffAt_const.mul (hψ₁.add hψ₂)`. Establish `hψτ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ((A'.chart j' ∘ h ∘ (A.chart j).symm) y)` using `by rwa [hτy]`. Establish `hτ2 : ContDiffAt ℝ 2 (A'.chart j' ∘ h ∘ (A.chart j).symm) y` using `(hτ.restrictScalars (𝕜 := ℝ)).contDiffAt`. Establish `hf : ContDiffAt ℝ 2 ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘ (A'.chart j' ∘ h ∘ (A.chart j).symm)) y` using `hψτ.comp y hτ2`. Establish `hg : ContDiffAt ℝ 2 (fun t => (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re) y` using `Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt`.

Establish `hev : (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) =ᶠ[𝓝 y] fun t => ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘ (A'.chart j' ∘ h ∘ (A.chart j).symm)) t + c * (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re`. Establish `hcs : ContinuousAt (A.chart j).symm y` using `(A.chart j).continuousAt_symm hy`. Establish `hOx : ∀ᶠ t in 𝓝 y, (A.chart j).symm t ∈ W₁ ∩ W₂ ∩ th.U x ∩ th.U p ∩ h ⁻¹' (A'.chart j').source`. Apply `hcs.eventually_mem` to reduce the goal to its premises. Rewrite using `[← hp]`.

Use `IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hpW₁, hpW₂⟩, hyU⟩, th.mem_U p⟩, hj'⟩` and prove the remaining obligations. Conclude with `(((hW₁o.inter hW₂o).inter (th.isOpen_U x)).inter (th.isOpen_U p)).inter ((A'.chart j').open_source.preimage hh.1)`. Use `filter_upwards [hOx] with t ht`. Take `⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩` from `ht`. Establish `e1` using `hE₁ _ ⟨⟨h1, h3⟩, h4⟩`.

Establish `e2 : th.φ p ((A.chart j).symm t) - th'.φ (h p) (h ((A.chart j).symm t)) = (G₂ ((A.chart j).symm t)).re` using `hE₂ _ h2`. Establish `e3 : (A'.chart j').symm (A'.chart j' (h ((A.chart j).symm t))) = h ((A.chart j).symm t)` using `(A'.chart j').left_inv h5`. Simplify using `only [Function.comp_apply, e3, Complex.add_re]`. Rewrite using `[← e1, ← e2]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨j', A'.chart j' (h p), fderiv ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y w, hy', hsy', ?_⟩` and prove the remaining obligations. Rewrite using `[levi_congr hev w, levi_add_smul c hf hg w, levi_comp w hτ hψτ, levi_re_analytic hGa w, hτy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_pull_eq {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ)
    (hth : IsPotential A th) (hth' : IsPotential A' th') (hu : A'.Smooth u)
    (hs : SamePot A Set.univ th (th'.pullback h hh.1)) (c : ℝ) (x : X) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ th.U x) (w : Fin e → ℂ) :
    ∃ (j' : Fin A'.n) (y' v : Fin e' → ℂ), y' ∈ (A'.chart j').target ∧
      (A'.chart j').symm y' = h ((A.chart j).symm y) ∧
      levi (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) y w =
        levi (fun s => c * (th'.φ (h ((A.chart j).symm y)) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) y' v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  obtain ⟨p, hp⟩ : ∃ p, p = (A.chart j).symm y := ⟨_, rfl⟩
  rw [← hp] at hyU ⊢
  obtain ⟨j', hj'⟩ := A'.cover (h p)
  obtain ⟨W₁, hW₁o, hpW₁, G₁, hG₁, hE₁⟩ := hth.2 x p p ⟨hyU, th.mem_U p⟩
  obtain ⟨W₂, hW₂o, hpW₂, G₂, hG₂, hE₂⟩ := hs p (Set.mem_univ p)
  have hτ : AnalyticAt ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    hh.2 j j' y ⟨hy, by simpa [← hp] using hj'⟩
  have hGa : AnalyticAt ℂ (fun t => G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)) y :=
    AnalyticAt.add (hG₁ j y ⟨hy, by simpa [← hp] using hpW₁⟩) (hG₂ j y ⟨hy, by simpa [← hp] using hpW₂⟩)
  have hτy : (A'.chart j' ∘ h ∘ (A.chart j).symm) y = A'.chart j' (h p) := by simp [← hp]
  have hy' : A'.chart j' (h p) ∈ (A'.chart j').target := (A'.chart j').map_source hj'
  have hsy' : (A'.chart j').symm (A'.chart j' (h p)) = h p := (A'.chart j').left_inv hj'

  have hψ₁ : ContDiffAt ℝ 2 (th'.φ (h p) ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p)) :=
      (A'.chart j').isOpen_inter_preimage_symm (th'.isOpen_U _)
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p) :=
      ⟨hy', by simpa [hsy'] using th'.mem_U (h p)⟩
    exact (((hth'.1 (h p) j').contDiffAt (hO.mem_nhds hm))).of_le h2
  have hψ₂ : ContDiffAt ℝ 2 (u ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ) := by
      simpa using (A'.chart j').open_target
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ :=
      ⟨hy', Set.mem_univ _⟩
    exact ((hu j').contDiffAt (hO.mem_nhds hm)).of_le h2
  have hψ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      (A'.chart j' (h p)) :=
    contDiffAt_const.mul (hψ₁.add hψ₂)
  have hψτ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      ((A'.chart j' ∘ h ∘ (A.chart j).symm) y) := by rwa [hτy]
  have hτ2 : ContDiffAt ℝ 2 (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    (hτ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hf : ContDiffAt ℝ 2 ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
      (A'.chart j' ∘ h ∘ (A.chart j).symm)) y := hψτ.comp y hτ2
  have hg : ContDiffAt ℝ 2 (fun t => (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt

  have hev : (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) =ᶠ[𝓝 y]
      fun t => ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
        (A'.chart j' ∘ h ∘ (A.chart j).symm)) t + c * (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re := by
    have hcs : ContinuousAt (A.chart j).symm y := (A.chart j).continuousAt_symm hy
    have hOx : ∀ᶠ t in 𝓝 y, (A.chart j).symm t ∈ W₁ ∩ W₂ ∩ th.U x ∩ th.U p ∩ h ⁻¹' (A'.chart j').source := by
      apply hcs.eventually_mem
      rw [← hp]
      refine IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hpW₁, hpW₂⟩, hyU⟩, th.mem_U p⟩, hj'⟩
      exact (((hW₁o.inter hW₂o).inter (th.isOpen_U x)).inter (th.isOpen_U p)).inter
        ((A'.chart j').open_source.preimage hh.1)
    filter_upwards [hOx] with t ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    have e1 := hE₁ _ ⟨⟨h1, h3⟩, h4⟩
    have e2 : th.φ p ((A.chart j).symm t) - th'.φ (h p) (h ((A.chart j).symm t)) =
      (G₂ ((A.chart j).symm t)).re := hE₂ _ h2
    have e3 : (A'.chart j').symm (A'.chart j' (h ((A.chart j).symm t))) = h ((A.chart j).symm t) :=
      (A'.chart j').left_inv h5
    simp only [Function.comp_apply, e3, Complex.add_re]
    rw [← e1, ← e2]
    ring
  refine ⟨j', A'.chart j' (h p), fderiv ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y w, hy', hsy', ?_⟩
  rw [levi_congr hev w, levi_add_smul c hf hg w, levi_comp w hτ hψτ, levi_re_analytic hGa w, hτy]
  ring

/- English proof (translation)
Introduce `e e' X Z _ _ A A' h hh th th' u hth hth' hu hs`. Use `⟨fun H x j y hy w => ?_, fun H x j y hy w => ?_⟩` and prove the remaining obligations. Take `⟨j', y', v, hy', hsy, hl⟩` from `levi_pull_eq A A' h hh th th' u hth hth' hu hs 1 x j y hy.1 hy.2.1 w`. Establish `hH` using `H (h ((A.chart j).symm y)) j' y' ⟨hy', by`. Rewrite using `[Set.mem_preimage, hsy]`.

Conclude with `LocPot.mem_U _ _⟩ v`. Simplify using `only [one_mul] at hl`. Conclude with `hl ▸ hH`. Take `⟨j', y', v, hy', hsy, hl⟩` from `levi_pull_eq A A' h hh th th' u hth hth' hu hs (-1) x j y hy.1 hy.2.1 w`. Establish `hH` using `H (h ((A.chart j).symm y)) j' y' ⟨hy', by`.

Rewrite using `[Set.mem_preimage, hsy]`. Conclude with `LocPot.mem_U _ _⟩ v`. Conclude with `hl ▸ hH`.
-/
theorem isPsh_pull : ∀ (e e' : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ),
    IsPotential A th → IsPotential A' th' → A'.Smooth u → SamePot A Set.univ th (th'.pullback h hh.1) →
    (IsPsh A' (th' + LocPot.ofFun u) → IsPsh A (th + LocPot.ofFun (u ∘ h))) ∧
      (IsPsh A' ((th' + LocPot.ofFun u).rsmul (-1)) → IsPsh A ((th + LocPot.ofFun (u ∘ h)).rsmul (-1))) := by
  intro e e' X Z _ _ A A' h hh th th' u hth hth' hu hs
  refine ⟨fun H x j y hy w => ?_, fun H x j y hy w => ?_⟩
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs 1 x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    simp only [one_mul] at hl
    exact hl ▸ hH
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs (-1) x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    exact hl ▸ hH

end GlobalTheory.CompanionTheory.Ar.PB.PshPull
