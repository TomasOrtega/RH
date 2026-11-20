import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

/- English proof (translation)
Introduce `II Ψ hΨ K hK ι hι Ω hΩ hQΩ E hE1 hE2 D M g hg z₀ hz₀`. Use `set S := mcPts (mCoordIdeal D.y) with hS`. Use `set x₀ := M.proj z₀ with hx₀`. Take `⟨j, hj⟩` from `M.atlas.cover x₀`. Use `set e := M.atlas.chart j with he`.

Take `⟨W, hWo, hxW, s, hs, hsh⟩` from `M.sections x₀`. Take `⟨N, hNo, hzN, κ, hκa, hκt, hκi⟩` from `hL K ι Ω D.y D.n D.arith D.smoothGeneric z₀ hz₀`. Use `set σ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hσ`. Use `set f : (Fin D.n → ℂ) → (Fin D.n → ℂ) := fun u => κ (σ u) with hf`. Use `set u₀ := e x₀ with hu₀`.

Use `set T := e.target ∩ e.symm ⁻¹' W with hT`. Establish `hTo : IsOpen T` using `e.isOpen_inter_preimage_symm hWo`. Establish `hσa : AnalyticOnNhd ℂ σ T` using `fun u hu => AnalyticAt.pi fun p => hsh p j u hu`. Establish `hu₀t : u₀ ∈ e.target` using `e.map_source hj`. Establish `hsymm₀ : e.symm u₀ = x₀` using `e.left_inv hj`.

Establish `hu₀T : u₀ ∈ T` using `⟨hu₀t, by simp only [Set.mem_preimage, hsymm₀]; exact hxW⟩`. Establish `hσ₀ : σ u₀ = s x₀` using `by simp only [hσ, hsymm₀]`. Take `⟨hsx₀S, hsx₀p⟩` from `hs x₀ hxW`. Take `⟨c₀, hc₀, hc₀e⟩` from `(M.fibre z₀ hz₀ (s x₀) hsx₀S).1 hsx₀p.symm`. Establish `hsx₀N : s x₀ ∈ N` using `hc₀e ▸ (hκt z₀ hzN c₀ hc₀).1`.

Establish `hκs₀ : κ (s x₀) = κ z₀` using `hc₀e ▸ (hκt z₀ hzN c₀ hc₀).2`. Use `set T' := T ∩ σ ⁻¹' N with hT'`. Establish `hT'o : IsOpen T'` using `hσa.continuousOn.isOpen_inter_preimage hTo hNo`. Establish `hu₀T' : u₀ ∈ T'` using `⟨hu₀T, by simp only [Set.mem_preimage, hσ₀]; exact hsx₀N⟩`. Establish `hfa : AnalyticOnNhd ℂ f T'` using `fun u hu => (hκa (σ u) hu.2).comp (hσa u hu.1)`.

Establish `hinj : Set.InjOn f T'`. Introduce `u hu u' hu' hfu`. Take `⟨hmS, hmp⟩` from `hs (e.symm u) hu.1.2`. Take `⟨hmS', hmp'⟩` from `hs (e.symm u') hu'.1.2`. Take `⟨c, hc, hce⟩` from `hκi (σ u) ⟨hu.2, hmS⟩ (σ u') ⟨hu'.2, hmS'⟩ hfu`.

Establish `hpe : M.proj (σ u) = M.proj (σ u')` using `(M.fibre (σ u) hmS (σ u') hmS').2 ⟨c, hc, hce⟩`. Establish `h2 : e.symm u = e.symm u'`. Simplify using `only [hσ] at hpe`. Rewrite using `[← hmp, ← hmp', hpe]`. Rewrite using `[← e.right_inv hu.1.1, ← e.right_inv hu'.1.1, h2]`.

Establish `hDinj : Function.Injective (fderiv ℂ f u₀)` using `hO D.n f T' hT'o hfa hinj u₀ hu₀T'`. Use `set Lc : (Fin D.n → ℂ) ≃L[ℂ] (Fin D.n → ℂ) := (LinearEquiv.ofInjectiveEndo (fderiv ℂ f u₀ : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)) hDinj).toContinuousLinearEquiv with hLc`. Establish `hFD : HasFDerivAt f (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) u₀`. Establish `hcoe : (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) = fderiv ℂ f u₀`. Use extensionality with `v`.

Both sides reduce to the same expression. Rewrite using `[hcoe]`. Conclude with `(hfa u₀ hu₀T').differentiableAt.hasFDerivAt`. Establish `hcd : ContDiffAt ℂ ω f u₀` using `(hfa u₀ hu₀T').contDiffAt`. Establish `hn : (ω : WithTop ℕ∞) ≠ 0` using `by simp`.

Use `set linv := hcd.localInverse hFD hn with hlinv`. Establish `hlinv_cd : ContDiffAt ℂ ω linv (f u₀)` using `hcd.to_localInverse hFD hn`. Establish `hlinv₀ : linv (f u₀) = u₀` using `hcd.localInverse_apply_image hFD hn`. Establish `hleft : ∀ᶠ u in 𝓝 u₀, linv (f u) = u` using `(hcd.hasStrictFDerivAt' hFD hn).eventually_left_inverse`. Establish `hfu₀ : f u₀ = κ z₀` using `by simp only [hf, hσ₀, hκs₀]`.

Use `set Φ : ((Σ k, ι k) → ℂ) → (Fin D.n → ℂ) := fun z => linv (κ z) with hΦ`. Establish `hΦcd : ContDiffAt ℂ ω Φ z₀`. Establish `h1 : ContDiffAt ℂ ω linv (κ z₀)` using `hfu₀ ▸ hlinv_cd`. Conclude with `h1.comp z₀ (hκa z₀ hzN).contDiffAt`. Establish `hΦ₀ : Φ z₀ = u₀` using `by simp only [hΦ, ← hfu₀, hlinv₀]`.

Take `⟨V₁, hV₁, hΦV₁⟩` from `hΦcd.contDiffOn (m := ∞) le_top (fun _ => rfl)`. Establish `hΦV₁R : ContDiffOn ℝ ∞ Φ V₁` using `hΦV₁.restrict_scalars ℝ`. Use `set V₂ := V₁ ∩ Φ ⁻¹' e.target with hV₂`. Establish `hV₂n : V₂ ∈ 𝓝 z₀` using `inter_mem hV₁ (hΦcd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hΦ₀ ▸ hu₀t)))`. Establish `hgs : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target`.

Use `hg j` as an intermediate fact. Simplify `this` using `[ReciprocityTheory.AnForm.M.FinHolAtlas.Smooth, ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn]`. Establish `hGV₂ : ContDiffOn ℝ ∞ (fun z => g (e.symm (Φ z))) V₂` using `hgs.comp (hΦV₁R.mono Set.inter_subset_left) (fun z hz => hz.2)`. Establish `hcont : ContinuousWithinAt M.proj S z₀` using `M.cont z₀ hz₀`. Establish `htend : Tendsto (fun w => e (M.proj w)) (𝓝[S] z₀) (𝓝 u₀)` using `(e.continuousAt hj).tendsto.comp hcont.tendsto`.

Establish `hev1 : ∀ᶠ w in 𝓝[S] z₀, M.proj w ∈ e.source ∩ W` using `hcont.tendsto ((e.open_source.inter hWo).mem_nhds ⟨hj, hxW⟩)`. Establish `hev2 : ∀ᶠ w in 𝓝[S] z₀, linv (f (e (M.proj w))) = e (M.proj w)` using `htend.eventually hleft`. Establish `hev3 : ∀ᶠ w in 𝓝[S] z₀, w ∈ N` using `nhdsWithin_le_nhds (hNo.mem_nhds hzN)`. Establish `hev : ∀ᶠ w in 𝓝[S] z₀, (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N` using `(hev1.and hev2).and hev3`. Rewrite `hev` using `[eventually_nhdsWithin_iff]`.

Use `⟨V₂ ∩ {w | w ∈ S → (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N}, inter_mem hV₂n hev, fun z => g (e.symm (Φ z)), hGV₂.mono Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Introduce and unpack `w ⟨⟨-, hw⟩, hwS⟩`. Take `⟨⟨⟨hxe, hxW'⟩, hli⟩, hwN⟩` from `hw hwS`. Take `⟨hsS, hsp⟩` from `hs (M.proj w) hxW'`. Take `⟨c, hc, hce⟩` from `(M.fibre w hwS (s (M.proj w)) hsS).1 hsp.symm`.

Establish `hfe : f (e (M.proj w)) = κ w`. Simplify using `only [hf, hσ, e.left_inv hxe]`. Rewrite using `[hce]`. Conclude with `(hκt w hwN c hc).2`. Establish `hΦw : Φ w = e (M.proj w)`.

Simplify using `only [hΦ]`. Rewrite using `[← hfe, hli]`. Simplify using `only [hΦw, e.left_inv hxe]`.
-/
theorem ProjSmoothAlong.proof (hO : HoloInjDerivInj.Statement) (hL : LocalOrbitChart.Statement) :
    ProjSmoothAlong.Statement := by
  intro II Ψ hΨ K hK ι hι Ω hΩ hQΩ E hE1 hE2 D M g hg z₀ hz₀
  set S := mcPts (mCoordIdeal D.y) with hS
  set x₀ := M.proj z₀ with hx₀
  obtain ⟨j, hj⟩ := M.atlas.cover x₀
  set e := M.atlas.chart j with he
  obtain ⟨W, hWo, hxW, s, hs, hsh⟩ := M.sections x₀
  obtain ⟨N, hNo, hzN, κ, hκa, hκt, hκi⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z₀ hz₀
  set σ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hσ
  set f : (Fin D.n → ℂ) → (Fin D.n → ℂ) := fun u => κ (σ u) with hf
  set u₀ := e x₀ with hu₀
  set T := e.target ∩ e.symm ⁻¹' W with hT
  have hTo : IsOpen T := e.isOpen_inter_preimage_symm hWo
  have hσa : AnalyticOnNhd ℂ σ T := fun u hu => AnalyticAt.pi fun p => hsh p j u hu
  have hu₀t : u₀ ∈ e.target := e.map_source hj
  have hsymm₀ : e.symm u₀ = x₀ := e.left_inv hj
  have hu₀T : u₀ ∈ T := ⟨hu₀t, by simp only [Set.mem_preimage, hsymm₀]; exact hxW⟩

  have hσ₀ : σ u₀ = s x₀ := by simp only [hσ, hsymm₀]
  obtain ⟨hsx₀S, hsx₀p⟩ := hs x₀ hxW
  obtain ⟨c₀, hc₀, hc₀e⟩ := (M.fibre z₀ hz₀ (s x₀) hsx₀S).1 hsx₀p.symm
  have hsx₀N : s x₀ ∈ N := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).1
  have hκs₀ : κ (s x₀) = κ z₀ := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).2

  set T' := T ∩ σ ⁻¹' N with hT'
  have hT'o : IsOpen T' := hσa.continuousOn.isOpen_inter_preimage hTo hNo
  have hu₀T' : u₀ ∈ T' := ⟨hu₀T, by simp only [Set.mem_preimage, hσ₀]; exact hsx₀N⟩
  have hfa : AnalyticOnNhd ℂ f T' := fun u hu => (hκa (σ u) hu.2).comp (hσa u hu.1)
  have hinj : Set.InjOn f T' := by
    intro u hu u' hu' hfu
    obtain ⟨hmS, hmp⟩ := hs (e.symm u) hu.1.2
    obtain ⟨hmS', hmp'⟩ := hs (e.symm u') hu'.1.2
    obtain ⟨c, hc, hce⟩ := hκi (σ u) ⟨hu.2, hmS⟩ (σ u') ⟨hu'.2, hmS'⟩ hfu
    have hpe : M.proj (σ u) = M.proj (σ u') := (M.fibre (σ u) hmS (σ u') hmS').2 ⟨c, hc, hce⟩
    have h2 : e.symm u = e.symm u' := by
      simp only [hσ] at hpe
      rw [← hmp, ← hmp', hpe]
    rw [← e.right_inv hu.1.1, ← e.right_inv hu'.1.1, h2]

  have hDinj : Function.Injective (fderiv ℂ f u₀) := hO D.n f T' hT'o hfa hinj u₀ hu₀T'
  set Lc : (Fin D.n → ℂ) ≃L[ℂ] (Fin D.n → ℂ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ f u₀ : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)) hDinj).toContinuousLinearEquiv
    with hLc
  have hFD : HasFDerivAt f (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) u₀ := by
    have hcoe : (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) = fderiv ℂ f u₀ := by
      ext v; rfl
    rw [hcoe]
    exact (hfa u₀ hu₀T').differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℂ ω f u₀ := (hfa u₀ hu₀T').contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set linv := hcd.localInverse hFD hn with hlinv
  have hlinv_cd : ContDiffAt ℂ ω linv (f u₀) := hcd.to_localInverse hFD hn
  have hlinv₀ : linv (f u₀) = u₀ := hcd.localInverse_apply_image hFD hn
  have hleft : ∀ᶠ u in 𝓝 u₀, linv (f u) = u := (hcd.hasStrictFDerivAt' hFD hn).eventually_left_inverse
  have hfu₀ : f u₀ = κ z₀ := by simp only [hf, hσ₀, hκs₀]

  set Φ : ((Σ k, ι k) → ℂ) → (Fin D.n → ℂ) := fun z => linv (κ z) with hΦ
  have hΦcd : ContDiffAt ℂ ω Φ z₀ := by
    have h1 : ContDiffAt ℂ ω linv (κ z₀) := hfu₀ ▸ hlinv_cd
    exact h1.comp z₀ (hκa z₀ hzN).contDiffAt
  have hΦ₀ : Φ z₀ = u₀ := by simp only [hΦ, ← hfu₀, hlinv₀]
  obtain ⟨V₁, hV₁, hΦV₁⟩ := hΦcd.contDiffOn (m := ∞) le_top (fun _ => rfl)
  have hΦV₁R : ContDiffOn ℝ ∞ Φ V₁ := hΦV₁.restrict_scalars ℝ
  set V₂ := V₁ ∩ Φ ⁻¹' e.target with hV₂
  have hV₂n : V₂ ∈ 𝓝 z₀ :=
    inter_mem hV₁ (hΦcd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hΦ₀ ▸ hu₀t)))
  have hgs : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target := by
    have := hg j
    simpa [ReciprocityTheory.AnForm.M.FinHolAtlas.Smooth, ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn] using this
  have hGV₂ : ContDiffOn ℝ ∞ (fun z => g (e.symm (Φ z))) V₂ :=
    hgs.comp (hΦV₁R.mono Set.inter_subset_left) (fun z hz => hz.2)

  have hcont : ContinuousWithinAt M.proj S z₀ := M.cont z₀ hz₀
  have htend : Tendsto (fun w => e (M.proj w)) (𝓝[S] z₀) (𝓝 u₀) :=
    (e.continuousAt hj).tendsto.comp hcont.tendsto
  have hev1 : ∀ᶠ w in 𝓝[S] z₀, M.proj w ∈ e.source ∩ W :=
    hcont.tendsto ((e.open_source.inter hWo).mem_nhds ⟨hj, hxW⟩)
  have hev2 : ∀ᶠ w in 𝓝[S] z₀, linv (f (e (M.proj w))) = e (M.proj w) := htend.eventually hleft
  have hev3 : ∀ᶠ w in 𝓝[S] z₀, w ∈ N := nhdsWithin_le_nhds (hNo.mem_nhds hzN)
  have hev : ∀ᶠ w in 𝓝[S] z₀, (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N :=
    (hev1.and hev2).and hev3
  rw [eventually_nhdsWithin_iff] at hev
  refine ⟨V₂ ∩ {w | w ∈ S → (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N},
    inter_mem hV₂n hev, fun z => g (e.symm (Φ z)), hGV₂.mono Set.inter_subset_left, ?_⟩
  rintro w ⟨⟨-, hw⟩, hwS⟩
  obtain ⟨⟨⟨hxe, hxW'⟩, hli⟩, hwN⟩ := hw hwS
  obtain ⟨hsS, hsp⟩ := hs (M.proj w) hxW'
  obtain ⟨c, hc, hce⟩ := (M.fibre w hwS (s (M.proj w)) hsS).1 hsp.symm
  have hfe : f (e (M.proj w)) = κ w := by
    simp only [hf, hσ, e.left_inv hxe]
    rw [hce]
    exact (hκt w hwN c hc).2
  have hΦw : Φ w = e (M.proj w) := by
    simp only [hΦ]
    rw [← hfe, hli]
  simp only [hΦw, e.left_inv hxe]

end GroundTheory.Heights₂.Heights.LowerBoundFree
