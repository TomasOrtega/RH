import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `K _ J _ II Ψ _ Ω _ _ W _ _ D M a k t ht hsrc`. Establish `hγ : AnalyticAt ℂ (D.chart a).γ t` using `(D.chart a).analytic t ht`. Establish `hev : ∀ᶠ t' in 𝓝 t, (D.chart a).γ t' ∈ mcPts (mCoordIdeal D.y)` using `Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds ht) fun t' h => (D.chart a).mem t' h`. Establish `hFan : AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t` using `LevelTowerAlt.analyticAt_proj D M (LevelTowerAlt.compat_atlas M.atlas k) hγ hev hsrc`. Use `⟨hFan, ?_⟩` and prove the remaining obligations.

Establish `htend : Tendsto (fun t' => M.proj ((D.chart a).γ t')) (𝓝 t) (𝓝 (M.proj ((D.chart a).γ t)))`. Establish `h1 : Tendsto (D.chart a).γ (𝓝 t) (𝓝[mcPts (mCoordIdeal D.y)] ((D.chart a).γ t))` using `tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto, hev⟩`. Conclude with `((M.cont _ ((D.chart a).mem t ht)).tendsto).comp h1`. Take `⟨U, hUo, hxU, s, hs, hsh⟩` from `M.sections (M.proj ((D.chart a).γ t))`. Establish `hHan : ∀ p, AnalyticAt ℂ (fun t' => s (M.proj ((D.chart a).γ t')) p) t` using `fun p => LevelTowerAlt.analyticAt_holoOn_proj D M (hsh p) hγ hev hxU`.

Set `P : (Σ kk, J kk) → ((Σ kk, J kk) → ℂ) →L[ℂ] ℂ` to `fun p => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ kk, J kk) => ℂ) p`. Establish `hγp : ∀ p, AnalyticAt ℂ (fun t' => (D.chart a).γ t' p) t` using `fun p => ((P p).analyticAt _).comp hγ`. Use `choose m hm using ((D.chart a).mem t ht).1`. Establish `hrel : ∀ᶠ t' in 𝓝 t, (∃ c : K → ℂ, (∀ kk, c kk ≠ 0) ∧ s (M.proj ((D.chart a).γ t')) = torusSmul c ((D.chart a).γ t')) ∧ ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0`. Establish `hU : ∀ᶠ t' in 𝓝 t, M.proj ((D.chart a).γ t') ∈ U` using `htend (hUo.mem_nhds hxU)`.

Establish `hnz : ∀ᶠ t' in 𝓝 t, ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0` using `Filter.eventually_all.mpr fun kk => (hγp ⟨kk, m kk⟩).continuousAt.eventually_ne (hm kk)`. Use `filter_upwards [hU, hev, hnz] with t' h1 h2 h3`. Use `⟨?_, h3⟩` and prove the remaining obligations. Take `⟨h4, h5⟩` from `hs _ h1`. Conclude with `(M.fibre _ h2 _ h4).mp h5.symm`.

Take `⟨cf, hcf⟩ : ∃ cf : (Fin D.n → ℂ) → K → ℂ, cf = fun t' kk => s (M.proj ((D.chart a).γ t')) ⟨kk, m kk⟩ / (D.chart a).γ t' ⟨kk, m kk⟩` from `⟨_, rfl⟩`. Establish `hcfeq : ∀ᶠ t' in 𝓝 t, ∀ p : (Σ kk, J kk), s (M.proj ((D.chart a).γ t')) p = cf t' p.1 * (D.chart a).γ t' p` using `by filter_upwards [hrel] with t' ht'`. Take `⟨⟨c, hc, he⟩, hn⟩` from `ht'`. Establish `hck : ∀ kk, cf t' kk = c kk`. Introduce `kk`.

Rewrite using `[hcf]`. Simplify using `only [he, torusSmul]`. Conclude with `mul_div_cancel_right₀ _ (hn kk)`. Introduce `p`. Rewrite using `[hck, he]`.

Both sides reduce to the same expression. Establish `hcf0 : ∀ kk, cf t kk ≠ 0`. Take `⟨⟨c, hc, he⟩, hn⟩` from `hrel.self_of_nhds`. Introduce `kk`. Rewrite using `[hcf]`.

Simplify using `only [he, torusSmul]`. Rewrite using `[mul_div_cancel_right₀ _ (hn kk)]`. Conclude with `hc kk`. Establish `hcfan : ∀ kk, AnalyticAt ℂ (fun t' => cf t' kk) t`. Introduce `kk`.

Rewrite using `[hcf]`. Conclude with `(hHan _).div (hγp _) (hm kk)`. Establish `hFt : M.atlas.chart k (M.proj ((D.chart a).γ t)) ∈ (M.atlas.chart k).target` using `(M.atlas.chart k).map_source hsrc`. Establish `hGan : ∀ p, AnalyticAt ℂ (fun y => s ((M.atlas.chart k).symm y) p) (M.atlas.chart k (M.proj ((D.chart a).γ t)))`. Introduce `p`.

Use `hsh p k _ ⟨hFt, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, (M.atlas.chart k).left_inv hsrc]`. Conclude with `hxU`. Establish `hG : DifferentiableAt ℂ (fun y => s ((M.atlas.chart k).symm y)) (M.atlas.chart k (M.proj ((D.chart a).γ t)))` using `differentiableAt_pi.mpr fun p => (hGan p).differentiableAt`. Establish `hHeq : (fun t' => s (M.proj ((D.chart a).γ t'))) =ᶠ[𝓝 t] (fun t' => s ((M.atlas.chart k).symm (M.atlas.chart k (M.proj ((D.chart a).γ t')))))` using `by filter_upwards [htend ((M.atlas.chart k).open_source.mem_nhds hsrc)] with t' h`.

Rewrite using `[(M.atlas.chart k).left_inv h]`. Use `set L := fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t with hL`. Use `set G' := fderiv ℂ (fun y => s ((M.atlas.chart k).symm y)) (M.atlas.chart k (M.proj ((D.chart a).γ t))) with hG'`. Establish `hc0` using `hG.hasFDerivAt.comp t hFan.differentiableAt.hasFDerivAt`. Establish `hH : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t'))) (G'.comp L) t` using `hc0.congr_of_eventuallyEq hHeq`.

Establish `hinj : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Apply `(D.chart a).immersion t ht v` to reduce the goal to its premises. Use `⟨fun kk => -(fderiv ℂ (fun t' => cf t' kk) t v) / cf t kk, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Establish `h1 : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t')) p) ((P p).comp (G'.comp L)) t` using `(P p).hasFDerivAt.comp t hH`. Establish `hγ' : HasFDerivAt (fun t' : Fin D.n → ℂ => (D.chart a).γ t' p) ((P p).comp (fderiv ℂ (D.chart a).γ t)) t` using `(P p).hasFDerivAt.comp t hγ.differentiableAt.hasFDerivAt`. Establish `h2` using `(hcfan p.1).differentiableAt.hasFDerivAt.mul hγ'`. Establish `h3` using `h2.congr_of_eventuallyEq (hcfeq.mono fun t' h => h p)`.

Establish `h4` using `DFunLike.congr_fun (h1.unique h3) v`. Simplify using `only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, P, ContinuousLinearMap.proj_apply] at h4`. Establish `h0` using `hcf0 p.1`. Establish `h5 : (0 : ℂ) = cf t p.1 * fderiv ℂ (D.chart a).γ t v p + (D.chart a).γ t p * fderiv ℂ (fun t' => cf t' p.1) t v` using `h4`. Use `show fderiv ℂ (D.chart a).γ t v p = -(fderiv ℂ (fun t' => cf t' p.1) t v) / cf t p.1 * (D.chart a).γ t p`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff h0]`. Take the linear combination `-h5`. Conclude with `⟨hinj, (LinearMap.injective_iff_surjective (f := (L : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)))).mp hinj⟩`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (a : Fin D.nCharts) (k : Fin M.atlas.n), ∀ t ∈ Metric.ball (0 : Fin D.n → ℂ) 1, M.proj ((D.chart a).γ t) ∈ (M.atlas.chart k).source → AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t ∧ Function.Bijective (fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M a k t ht hsrc
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t ht
  have hev : ∀ᶠ t' in 𝓝 t, (D.chart a).γ t' ∈ mcPts (mCoordIdeal D.y) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds ht) fun t' h => (D.chart a).mem t' h
  have hFan : AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t :=
    LevelTowerAlt.analyticAt_proj D M (LevelTowerAlt.compat_atlas M.atlas k) hγ hev hsrc
  refine ⟨hFan, ?_⟩
  have htend : Tendsto (fun t' => M.proj ((D.chart a).γ t')) (𝓝 t) (𝓝 (M.proj ((D.chart a).γ t))) := by
    have h1 : Tendsto (D.chart a).γ (𝓝 t) (𝓝[mcPts (mCoordIdeal D.y)] ((D.chart a).γ t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto, hev⟩
    exact ((M.cont _ ((D.chart a).mem t ht)).tendsto).comp h1
  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj ((D.chart a).γ t))
  have hHan : ∀ p, AnalyticAt ℂ (fun t' => s (M.proj ((D.chart a).γ t')) p) t :=
    fun p => LevelTowerAlt.analyticAt_holoOn_proj D M (hsh p) hγ hev hxU
  let P : (Σ kk, J kk) → ((Σ kk, J kk) → ℂ) →L[ℂ] ℂ := fun p =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ kk, J kk) => ℂ) p
  have hγp : ∀ p, AnalyticAt ℂ (fun t' => (D.chart a).γ t' p) t :=
    fun p => ((P p).analyticAt _).comp hγ
  choose m hm using ((D.chart a).mem t ht).1
  have hrel : ∀ᶠ t' in 𝓝 t, (∃ c : K → ℂ, (∀ kk, c kk ≠ 0) ∧
      s (M.proj ((D.chart a).γ t')) = torusSmul c ((D.chart a).γ t')) ∧
      ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0 := by
    have hU : ∀ᶠ t' in 𝓝 t, M.proj ((D.chart a).γ t') ∈ U := htend (hUo.mem_nhds hxU)
    have hnz : ∀ᶠ t' in 𝓝 t, ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0 :=
      Filter.eventually_all.mpr fun kk => (hγp ⟨kk, m kk⟩).continuousAt.eventually_ne (hm kk)
    filter_upwards [hU, hev, hnz] with t' h1 h2 h3
    refine ⟨?_, h3⟩
    obtain ⟨h4, h5⟩ := hs _ h1
    exact (M.fibre _ h2 _ h4).mp h5.symm
  obtain ⟨cf, hcf⟩ : ∃ cf : (Fin D.n → ℂ) → K → ℂ, cf = fun t' kk =>
      s (M.proj ((D.chart a).γ t')) ⟨kk, m kk⟩ / (D.chart a).γ t' ⟨kk, m kk⟩ := ⟨_, rfl⟩
  have hcfeq : ∀ᶠ t' in 𝓝 t, ∀ p : (Σ kk, J kk),
      s (M.proj ((D.chart a).γ t')) p = cf t' p.1 * (D.chart a).γ t' p := by
    filter_upwards [hrel] with t' ht'
    obtain ⟨⟨c, hc, he⟩, hn⟩ := ht'
    have hck : ∀ kk, cf t' kk = c kk := by
      intro kk
      rw [hcf]
      simp only [he, torusSmul]
      exact mul_div_cancel_right₀ _ (hn kk)
    intro p
    rw [hck, he]
    rfl
  have hcf0 : ∀ kk, cf t kk ≠ 0 := by
    obtain ⟨⟨c, hc, he⟩, hn⟩ := hrel.self_of_nhds
    intro kk
    rw [hcf]
    simp only [he, torusSmul]
    rw [mul_div_cancel_right₀ _ (hn kk)]
    exact hc kk
  have hcfan : ∀ kk, AnalyticAt ℂ (fun t' => cf t' kk) t := by
    intro kk
    rw [hcf]
    exact (hHan _).div (hγp _) (hm kk)
  have hFt : M.atlas.chart k (M.proj ((D.chart a).γ t)) ∈ (M.atlas.chart k).target :=
    (M.atlas.chart k).map_source hsrc
  have hGan : ∀ p, AnalyticAt ℂ (fun y => s ((M.atlas.chart k).symm y) p)
      (M.atlas.chart k (M.proj ((D.chart a).γ t))) := by
    intro p
    refine hsh p k _ ⟨hFt, ?_⟩
    simp only [Set.mem_preimage, (M.atlas.chart k).left_inv hsrc]
    exact hxU
  have hG : DifferentiableAt ℂ (fun y => s ((M.atlas.chart k).symm y))
      (M.atlas.chart k (M.proj ((D.chart a).γ t))) :=
    differentiableAt_pi.mpr fun p => (hGan p).differentiableAt
  have hHeq : (fun t' => s (M.proj ((D.chart a).γ t'))) =ᶠ[𝓝 t]
      (fun t' => s ((M.atlas.chart k).symm (M.atlas.chart k (M.proj ((D.chart a).γ t'))))) := by
    filter_upwards [htend ((M.atlas.chart k).open_source.mem_nhds hsrc)] with t' h
    rw [(M.atlas.chart k).left_inv h]
  set L := fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t with hL
  set G' := fderiv ℂ (fun y => s ((M.atlas.chart k).symm y))
    (M.atlas.chart k (M.proj ((D.chart a).γ t))) with hG'
  have hc0 := hG.hasFDerivAt.comp t hFan.differentiableAt.hasFDerivAt
  have hH : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t'))) (G'.comp L) t :=
    hc0.congr_of_eventuallyEq hHeq
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply (D.chart a).immersion t ht v
    refine ⟨fun kk => -(fderiv ℂ (fun t' => cf t' kk) t v) / cf t kk, ?_⟩
    funext p
    have h1 : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t')) p)
        ((P p).comp (G'.comp L)) t :=
      (P p).hasFDerivAt.comp t hH
    have hγ' : HasFDerivAt (fun t' : Fin D.n → ℂ => (D.chart a).γ t' p)
        ((P p).comp (fderiv ℂ (D.chart a).γ t)) t :=
      (P p).hasFDerivAt.comp t hγ.differentiableAt.hasFDerivAt
    have h2 := (hcfan p.1).differentiableAt.hasFDerivAt.mul hγ'
    have h3 := h2.congr_of_eventuallyEq (hcfeq.mono fun t' h => h p)
    have h4 := DFunLike.congr_fun (h1.unique h3) v
    simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, P, ContinuousLinearMap.proj_apply] at h4
    have h0 := hcf0 p.1
    have h5 : (0 : ℂ) = cf t p.1 * fderiv ℂ (D.chart a).γ t v p +
        (D.chart a).γ t p * fderiv ℂ (fun t' => cf t' p.1) t v := h4
    show fderiv ℂ (D.chart a).γ t v p = -(fderiv ℂ (fun t' => cf t' p.1) t v) / cf t p.1 * (D.chart a).γ t p
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    linear_combination -h5
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (L : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)))).mp hinj⟩
