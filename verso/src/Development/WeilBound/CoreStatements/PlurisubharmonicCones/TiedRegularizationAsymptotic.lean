import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtLogH

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

open GroundTheory.Heights₂.Heights.Regular (PotentialCharts contDiffAt_comp_symm_of_smoothOn)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W) (M : XModel D)

/- English proof (translation)
Use `filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (D.chart a).mem s hs`.
-/
theorem eventually_mem (a : Fin D.nCharts) {t : Fin D.n → ℂ} (ht : t ∈ Metric.ball (0 : Fin D.n → ℂ) 1) :
    ∀ᶠ s : Fin D.n → ℂ in 𝓝 t, (D.chart a).γ s ∈ mcPts (mCoordIdeal D.y) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (D.chart a).mem s hs

/- English proof (translation)
Use `set y0 := M.proj (g t) with hy0`. Take `⟨U, hUo, hyU, hUth, s, hs, hsholo, G1, hG1, hG1eq⟩` from `hth y0 y0 (P.th.mem_U y0)`. Take `⟨W', hWo, hyW, G2, hG2, hG2eq⟩` from `P.q_th k y0 y0 ⟨P.th.mem_U y0, hk⟩`. Use `set F : (Fin D.n → ℂ) → Fin D.n → ℂ := fun s' => P.chart k (M.proj (g s')) with hF`. Establish `hFan : AnalyticAt ℂ F t` using `analyticAt_proj D M (P.compat k) hg hm hk`.

Establish `hpc : ContinuousAt (fun s' => M.proj (g s')) t` using `continuousAt_proj M hg.continuousAt hm`. Establish `hev_set : ∀ᶠ s' in 𝓝 t, M.proj (g s') ∈ U ∩ W' ∩ P.th.U y0 ∩ (P.chart k).source` using `hpc.preimage_mem_nhds (IsOpen.mem_nhds (((hUo.inter hWo).inter (P.th.isOpen_U y0)).inter (P.chart k).open_source) ⟨⟨⟨hyU, hyW⟩, P.th.mem_U y0⟩, hk⟩)`. Establish `hsan : ∀ p, AnalyticAt ℂ (fun s' => s (M.proj (g s')) p) t` using `fun p => analyticAt_holoOn_proj D M (hsholo p) hg hm hyU`. Establish `hgan : ∀ p, AnalyticAt ℂ (fun s' => g s' p) t` using `fun p => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp hg`. Establish `hs0` using `(hs y0 hyU).1`.

Use `choose i hi using hs0.1`. Establish `hgt` using `(M.fibre (s y0) hs0 (g t) hm.self_of_nhds).1 (hs y0 hyU).2`. Take `⟨c0, hc0, hgt_eq⟩` from `hgt`. Use `set c : (Fin D.n → ℂ) → K → ℂ := fun s' k' => g s' ⟨k', i k'⟩ / s (M.proj (g s')) ⟨k', i k'⟩ with hc`. Establish `hct : ∀ k', c t k' = c0 k'`.

Introduce `k'`. Use `show g t ⟨k', i k'⟩ / s y0 ⟨k', i k'⟩ = c0 k'`. Rewrite using `[hgt_eq]`. Simplify using `only [torusSmul]`. Clear denominators, using `[hi k']` for the nonvanishing conditions.

Establish `hcan : ∀ k', AnalyticAt ℂ (fun s' => c s' k') t` using `fun k' => (hgan _).div (hsan _) (hi k')`. Establish `hden : ∀ᶠ s' in 𝓝 t, ∀ k', s (M.proj (g s')) ⟨k', i k'⟩ ≠ 0`. Rewrite using `[Filter.eventually_all]`. Introduce `k'`. Conclude with `(hsan _).continuousAt.eventually_ne (hi k')`.

Establish `hslit : ∀ᶠ s' in 𝓝 t, ∀ k', c s' k' / c t k' ∈ Complex.slitPlane`. Rewrite using `[Filter.eventually_all]`. Introduce `k'`. Establish `hcont : ContinuousAt (fun s' => c s' k' / c t k') t` using `(AnalyticAt.div_const (hcan k') : AnalyticAt ℂ (fun s' => c s' k' / c t k') t).continuousAt`. Establish `h1 : c t k' / c t k' ∈ Complex.slitPlane`.

Rewrite using `[div_self (by rw [hct]; exact hc0 k')]; exact Complex.one_mem_slitPlane`. Conclude with `hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds h1)`. Use `set G : (Fin D.n → ℂ) → ℂ := fun s' => ∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ)) - G1 (M.proj (g s')) - G2 (M.proj (g s')) with hG`. Establish `hGan : AnalyticAt ℂ G t`. Establish `hsum : AnalyticAt ℂ (fun s' => ∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))) t`.

Establish `hs'` using `Finset.analyticAt_sum (𝕜 := ℂ) (c := t) (f := fun k' (s' : Fin D.n → ℂ) => (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))) Finset.univ (fun k' _ => analyticAt_const.mul ((AnalyticAt.clog (AnalyticAt.div_const (hcan k')) (hslit.self_of_nhds k')).add an …`. Use `hs' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s'`. Simplify using `[Finset.sum_apply]`. Conclude with `(hsum.sub (analyticAt_holoOn_proj D M hG1 hg hm hyU)).sub (analyticAt_holoOn_proj D M hG2 hg hm hyW)`.

Establish `hq : ContDiffAt ℝ 2 (P.chartFun φ k) (F t)`. Establish `h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.q k) (F t)` using `(P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds ((P.chart k).map_source hk))`. Establish `h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ ∘ (P.chart k).symm) (F t)` using `GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (P.compat k) isOpen_univ hφ (Set.mem_univ _) hk`. Conclude with `(h1.add h2).of_le (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))`. Establish `hcomp : ContDiffAt ℝ 2 (P.chartFun φ k ∘ F) t` using `hq.comp t (hFan.contDiffAt.restrict_scalars ℝ)`.

Establish `hev : ∀ᶠ s' in 𝓝 t, Real.log (ref.h (g s')) + φ (M.proj (g s')) = (P.chartFun φ k ∘ F) s' + (G s').re` using `by filter_upwards [hev_set, hden, hm] with s' hset hd hms`. Establish `hsz` using `hs _ hset.1.1.1`. Take `⟨c', hc', hgeq⟩` from `(M.fibre (s (M.proj (g s'))) hsz.1 (g s') hms).1 hsz.2`. Establish `hcc : ∀ k', c s' k' = c' k'` using `fun k' => by`. Establish `h` using `congrFun hgeq ⟨k', i k'⟩`.

Simplify using `only [torusSmul] at h`. Use `show g s' ⟨k', i k'⟩ / s (M.proj (g s')) ⟨k', i k'⟩ = c' k'`. Rewrite using `[h]`. Clear denominators, using `[hd k']` for the nonvanishing conditions. Establish `hlog` using `log_h_smul ref hsz.1.1 hc'`.

Rewrite `hlog` using `[← hgeq]`. Establish `e1` using `hG1eq _ hset.1.1.1`. Establish `e2` using `hG2eq _ ⟨⟨hset.1.1.2, hset.1.2⟩, hset.2⟩`. Establish `hsum : (∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))).re = ∑ k', (ref.a k' : ℝ) * Real.log ‖c' k'‖`. Rewrite using `[Complex.re_sum]`.

Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[hcc, hct]`. Simplify using `only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.log_re, Complex.ofReal_re, zero_mul, sub_zero]`. Rewrite using `[norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k')) (norm_ne_zero_iff.mpr (hc0 k'))]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hch : (P.chartFun φ k ∘ F) s' = P.q k (F s') + φ (M.proj (g s'))`. Simplify using `only [Function.comp, GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, hF]`. Rewrite using `[(P.chart k).left_inv hset.2]`. Rewrite using `[hch, hG]`. Simplify using `only [Complex.sub_re]`.

Rewrite using `[hsum, hlog]`. Simplify using `only [hF]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[levi_add_re hcomp hGan hev v, ReciprocityTheory.AnForm.levi_comp v hFan hq]`.
-/
theorem levi_chartFun_gen (P : PotentialCharts M.atlas) (ref : HermLine J) (hth : ThRef M ref P.th)
    {φ : M.Xc → ℝ} (hφ : M.atlas.Smooth φ) {g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ} {t : Fin D.n → ℂ}
    (hg : AnalyticAt ℂ g t) (hm : ∀ᶠ s in 𝓝 t, g s ∈ mcPts (mCoordIdeal D.y)) (k : Fin P.N)
    (hk : M.proj (g t) ∈ (P.chart k).source) (v : Fin D.n → ℂ) :
    levi (fun s => Real.log (ref.h (g s)) + φ (M.proj (g s))) t v =
      levi (P.chartFun φ k) (P.chart k (M.proj (g t))) (fderiv ℂ (fun s => P.chart k (M.proj (g s))) t v) := by
  classical
  set y0 := M.proj (g t) with hy0
  obtain ⟨U, hUo, hyU, hUth, s, hs, hsholo, G1, hG1, hG1eq⟩ := hth y0 y0 (P.th.mem_U y0)
  obtain ⟨W', hWo, hyW, G2, hG2, hG2eq⟩ := P.q_th k y0 y0 ⟨P.th.mem_U y0, hk⟩
  set F : (Fin D.n → ℂ) → Fin D.n → ℂ := fun s' => P.chart k (M.proj (g s')) with hF
  have hFan : AnalyticAt ℂ F t := analyticAt_proj D M (P.compat k) hg hm hk
  have hpc : ContinuousAt (fun s' => M.proj (g s')) t := continuousAt_proj M hg.continuousAt hm
  have hev_set : ∀ᶠ s' in 𝓝 t, M.proj (g s') ∈ U ∩ W' ∩ P.th.U y0 ∩ (P.chart k).source :=
    hpc.preimage_mem_nhds (IsOpen.mem_nhds (((hUo.inter hWo).inter (P.th.isOpen_U y0)).inter (P.chart k).open_source)
      ⟨⟨⟨hyU, hyW⟩, P.th.mem_U y0⟩, hk⟩)
  have hsan : ∀ p, AnalyticAt ℂ (fun s' => s (M.proj (g s')) p) t := fun p =>
    analyticAt_holoOn_proj D M (hsholo p) hg hm hyU
  have hgan : ∀ p, AnalyticAt ℂ (fun s' => g s' p) t := fun p =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp hg
  have hs0 := (hs y0 hyU).1
  choose i hi using hs0.1
  have hgt := (M.fibre (s y0) hs0 (g t) hm.self_of_nhds).1 (hs y0 hyU).2
  obtain ⟨c0, hc0, hgt_eq⟩ := hgt
  set c : (Fin D.n → ℂ) → K → ℂ := fun s' k' => g s' ⟨k', i k'⟩ / s (M.proj (g s')) ⟨k', i k'⟩ with hc
  have hct : ∀ k', c t k' = c0 k' := by
    intro k'
    show g t ⟨k', i k'⟩ / s y0 ⟨k', i k'⟩ = c0 k'
    rw [hgt_eq]
    simp only [torusSmul]
    field_simp [hi k']
  have hcan : ∀ k', AnalyticAt ℂ (fun s' => c s' k') t := fun k' => (hgan _).div (hsan _) (hi k')
  have hden : ∀ᶠ s' in 𝓝 t, ∀ k', s (M.proj (g s')) ⟨k', i k'⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro k'
    exact (hsan _).continuousAt.eventually_ne (hi k')
  have hslit : ∀ᶠ s' in 𝓝 t, ∀ k', c s' k' / c t k' ∈ Complex.slitPlane := by
    rw [Filter.eventually_all]
    intro k'
    have hcont : ContinuousAt (fun s' => c s' k' / c t k') t := (AnalyticAt.div_const (hcan k') : AnalyticAt ℂ (fun s' => c s' k' / c t k') t).continuousAt
    have h1 : c t k' / c t k' ∈ Complex.slitPlane := by
      rw [div_self (by rw [hct]; exact hc0 k')]; exact Complex.one_mem_slitPlane
    exact hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds h1)
  set G : (Fin D.n → ℂ) → ℂ := fun s' => ∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ)) - G1 (M.proj (g s')) - G2 (M.proj (g s')) with hG
  have hGan : AnalyticAt ℂ G t := by
    have hsum : AnalyticAt ℂ (fun s' => ∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))) t := by
      have hs' := Finset.analyticAt_sum (𝕜 := ℂ) (c := t)
        (f := fun k' (s' : Fin D.n → ℂ) => (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ)))
        Finset.univ (fun k' _ => analyticAt_const.mul
          ((AnalyticAt.clog (AnalyticAt.div_const (hcan k')) (hslit.self_of_nhds k')).add analyticAt_const))
      convert hs' using 1
      funext s'
      simp [Finset.sum_apply]
    exact (hsum.sub (analyticAt_holoOn_proj D M hG1 hg hm hyU)).sub (analyticAt_holoOn_proj D M hG2 hg hm hyW)
  have hq : ContDiffAt ℝ 2 (P.chartFun φ k) (F t) := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.q k) (F t) :=
      (P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds ((P.chart k).map_source hk))
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ ∘ (P.chart k).symm) (F t) :=
      GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (P.compat k) isOpen_univ hφ (Set.mem_univ _) hk
    exact (h1.add h2).of_le (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ 2 (P.chartFun φ k ∘ F) t :=
    hq.comp t (hFan.contDiffAt.restrict_scalars ℝ)
  have hev : ∀ᶠ s' in 𝓝 t, Real.log (ref.h (g s')) + φ (M.proj (g s')) = (P.chartFun φ k ∘ F) s' + (G s').re := by
    filter_upwards [hev_set, hden, hm] with s' hset hd hms
    have hsz := hs _ hset.1.1.1
    obtain ⟨c', hc', hgeq⟩ := (M.fibre (s (M.proj (g s'))) hsz.1 (g s') hms).1 hsz.2
    have hcc : ∀ k', c s' k' = c' k' := fun k' => by
      have h := congrFun hgeq ⟨k', i k'⟩
      simp only [torusSmul] at h
      show g s' ⟨k', i k'⟩ / s (M.proj (g s')) ⟨k', i k'⟩ = c' k'
      rw [h]
      field_simp [hd k']
    have hlog := log_h_smul ref hsz.1.1 hc'
    rw [← hgeq] at hlog
    have e1 := hG1eq _ hset.1.1.1
    have e2 := hG2eq _ ⟨⟨hset.1.1.2, hset.1.2⟩, hset.2⟩
    have hsum : (∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))).re =
        ∑ k', (ref.a k' : ℝ) * Real.log ‖c' k'‖ := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [hcc, hct]
      simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.log_re,
        Complex.ofReal_re, zero_mul, sub_zero]
      rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k')) (norm_ne_zero_iff.mpr (hc0 k'))]
      ring
    have hch : (P.chartFun φ k ∘ F) s' = P.q k (F s') + φ (M.proj (g s')) := by
      simp only [Function.comp, GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, hF]
      rw [(P.chart k).left_inv hset.2]
    rw [hch, hG]
    simp only [Complex.sub_re]
    rw [hsum, hlog]
    simp only [hF]
    linarith
  rw [levi_add_re hcomp hGan hev v, ReciprocityTheory.AnForm.levi_comp v hFan hq]

/- English proof (translation)
Establish `hball : ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2), t ∈ Metric.ball (0 : Fin D.n → ℂ) 1`. Introduce `t ht`. Rewrite `ht` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcont : ContinuousOn (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) (Metric.closedBall 0 (1 / 2))`. Introduce `t ht`. Establish `htb` using `hball t ht`. Conclude with `(continuousAt_proj M ((D.chart a).analytic t htb).continuousAt (eventually_mem D a htb)).continuousWithinAt`. Establish `hk : ∀ k : Fin P.N, ∃ C : ℝ, ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2) ∩ (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) ⁻¹' closure (P.inner k), ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C`.

Introduce `k`. Establish `hcl : IsClosed (Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2) ∩ (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) ⁻¹' closure (P.inner k))` using `hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_closure`. Establish `hcpt` using `(isCompact_closedBall (0 : Fin D.n → ℂ) (1 / 2)).of_isClosed_subset hcl Set.inter_subset_left`. Apply `hcpt.exists_bound_of_continuousOn` to reduce the goal to its premises. Introduce `t ht`.

Establish `htb` using `hball t ht.1`. Establish `hsrc : M.proj ((D.chart a).γ t) ∈ (P.chart k).source` using `P.mid_subset_source k (P.closure_inner k ht.2)`. Establish `hF` using `analyticAt_proj D M (P.compat k) ((D.chart a).analytic t htb) (eventually_mem D a htb) hsrc`. Conclude with `hF.fderiv.continuousAt.continuousWithinAt`. Use `choose C hC using hk`.

Use `⟨∑ k, |C k|, fun t ht => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `P.cover (M.proj ((D.chart a).γ t))`. Use `⟨k, P.closure_inner k (subset_closure hk), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_deriv_bound (P : PotentialCharts M.atlas) (a : Fin D.nCharts) :
    ∃ C : ℝ, ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2), ∃ k, M.proj ((D.chart a).γ t) ∈ P.mid k ∧
      ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C := by
  have hball : ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2), t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := by
    intro t ht
    rw [Metric.mem_closedBall] at ht
    rw [Metric.mem_ball]
    linarith
  have hcont : ContinuousOn (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) (Metric.closedBall 0 (1 / 2)) := by
    intro t ht
    have htb := hball t ht
    exact (continuousAt_proj M ((D.chart a).analytic t htb).continuousAt (eventually_mem D a htb)).continuousWithinAt
  have hk : ∀ k : Fin P.N, ∃ C : ℝ, ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2) ∩
      (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) ⁻¹' closure (P.inner k),
      ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C := by
    intro k
    have hcl : IsClosed (Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2) ∩
        (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) ⁻¹' closure (P.inner k)) :=
      hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_closure
    have hcpt := (isCompact_closedBall (0 : Fin D.n → ℂ) (1 / 2)).of_isClosed_subset hcl Set.inter_subset_left
    apply hcpt.exists_bound_of_continuousOn
    intro t ht
    have htb := hball t ht.1
    have hsrc : M.proj ((D.chart a).γ t) ∈ (P.chart k).source :=
      P.mid_subset_source k (P.closure_inner k ht.2)
    have hF := analyticAt_proj D M (P.compat k) ((D.chart a).analytic t htb) (eventually_mem D a htb) hsrc
    exact hF.fderiv.continuousAt.continuousWithinAt
  choose C hC using hk
  refine ⟨∑ k, |C k|, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := P.cover (M.proj ((D.chart a).γ t))
  refine ⟨k, P.closure_inner k (subset_closure hk), ?_⟩
  calc ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C k :=
        hC k t ⟨ht, subset_closure hk⟩
    _ ≤ |C k| := le_abs_self _
    _ ≤ ∑ k, |C k| := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ k)

/- English proof (translation)
Establish `hK : ∀ j, ∃ ε > (0 : ℝ), Metric.cthickening ε (P.chart j '' closure (P.mid j)) ⊆ (P.chart j).target`. Introduce `j`. Establish `hc : IsCompact (P.chart j '' closure (P.mid j))` using `(isClosed_closure.isCompact).image_of_continuousOn ((P.chart j).continuousOn.mono (P.closure_mid j))`. Establish `hsub : P.chart j '' closure (P.mid j) ⊆ (P.chart j).target`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `(P.chart j).map_source (P.closure_mid j hx)`. Conclude with `hc.exists_cthickening_subset_open (P.chart j).open_target hsub`. Use `choose ε hε hsub using hK`. Rewrite using `[Filter.eventually_all]`. Introduce `j`.

Use `filter_upwards [Ioo_mem_nhdsGT (hε j)] with t ht x hx`. Conclude with `(Metric.closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans ((Metric.cthickening_mono ht.2.le _).trans (hsub j))`.
-/
theorem eventually_closedBall_subset (P : PotentialCharts M.atlas) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (P.mid j),
      Metric.closedBall (P.chart j x) t ⊆ (P.chart j).target := by
  have hK : ∀ j, ∃ ε > (0 : ℝ), Metric.cthickening ε (P.chart j '' closure (P.mid j)) ⊆ (P.chart j).target := by
    intro j
    have hc : IsCompact (P.chart j '' closure (P.mid j)) :=
      (isClosed_closure.isCompact).image_of_continuousOn ((P.chart j).continuousOn.mono (P.closure_mid j))
    have hsub : P.chart j '' closure (P.mid j) ⊆ (P.chart j).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact (P.chart j).map_source (P.closure_mid j hx)
    exact hc.exists_cthickening_subset_open (P.chart j).open_target hsub
  choose ε hε hsub using hK
  rw [Filter.eventually_all]
  intro j
  filter_upwards [Ioo_mem_nhdsGT (hε j)] with t ht x hx
  exact (Metric.closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((Metric.cthickening_mono ht.2.le _).trans (hsub j))

end

/- English proof (translation)
Introduce `K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hT δ hδ`. Establish `hC` using `fun a => exists_deriv_bound D M S'.B.toPotentialCharts a`. Use `choose C hC using hC`. Use `set C0 : ℝ := ∑ a, |C a| with hC0`. Establish `hC0nn : 0 ≤ C0` using `Finset.sum_nonneg fun a _ => abs_nonneg _`.

Establish `hCle : ∀ a, C a ≤ C0` using `fun a => (le_abs_self _).trans (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) (Finset.mem_univ a))`. Use `set Cη : ℝ := max S'.Cη 0 with hCη`. Establish `hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 4 * Cη * S'.e1 t * C0 ^ 2 < δ`. Establish `h0 : Tendsto (fun t => 4 * Cη * S'.e1 t * C0 ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Cη * 0 * C0 ^ 2))` using `((hT.e1_tendsto_zero.const_mul (4 * Cη)).mul_const (C0 ^ 2))`. Rewrite `h0` using `[mul_zero, zero_mul]`.

Conclude with `(tendsto_order.1 h0).2 δ hδ`. Use `filter_upwards [self_mem_nhdsWithin, hT.compare, eventually_closedBall_subset D M S'.B.toPotentialCharts, hsmall] with t' ht' hcmp hball hsm`. Establish `hε : 0 < S'.e1 t'` using `lt_of_lt_of_le ht' (S'.e1_ge t' ht')`. Take `⟨hsmooth, hlev⟩` from `GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc D.n M.atlas S'.B S'.ρ S'.η S'.Cη t' (S'.e1 t') S'.cutoff ht' hε hball hcmp`. Introduce `a t ht v`.

Establish `htb : t ∈ Metric.ball (0 : Fin D.n → ℂ) 1`. Rewrite using `[mem_ball_zero_iff]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk, hbd⟩` from `hC a t (mem_closedBall_zero_iff.2 ht)`. Establish `hl : levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v = levi (S'.B.toPotentialCharts.chartFun (S'.bregWeight t') k) (S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ t))) (fderiv ℂ (fun s => S'.B.toPotentia …` using `levi_chartFun_gen D M S'.B.toPotentialCharts S'.ref S'.th_ref hsmooth ((D.chart a).analytic t htb) (eventually_mem D a htb) k (GroundTheory.Heights₂.Heights.Regular.PotentialCharts.mid_subset_source _ k hk) v`.

Rewrite using `[hl]`. Use `set X := fderiv ℂ (fun s => S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ s))) t v with hX`. Establish `hlow` using `hlev k _ hk X`. Establish `hXn : ‖X‖ ≤ C0 * ‖v‖` using `(ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbd.trans (hCle a)) (norm_nonneg _))`. Establish `hX2 : ‖X‖ ^ 2 ≤ C0 ^ 2 * ‖v‖ ^ 2`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hXn 2`. Establish `hCη1 : S'.Cη ≤ Cη` using `le_max_left _ _`. Establish `hCη0 : 0 ≤ Cη` using `le_max_right _ _`. Establish `h1 : 4 * S'.Cη * S'.e1 t' * ‖X‖ ^ 2 ≤ 4 * Cη * S'.e1 t' * ‖X‖ ^ 2` using `by gcongr`.

Establish `h2 : 4 * Cη * S'.e1 t' * ‖X‖ ^ 2 ≤ 4 * Cη * S'.e1 t' * (C0 ^ 2 * ‖v‖ ^ 2)` using `by gcongr`. Establish `h3 : 4 * Cη * S'.e1 t' * (C0 ^ 2 * ‖v‖ ^ 2) ≤ δ * ‖v‖ ^ 2`. Rewrite using `[← _root_.mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right hsm.le (sq_nonneg _)`. Establish `h4 : -(δ * ‖v‖ ^ 2) ≤ -(4 * S'.Cη * S'.e1 t') * ‖X‖ ^ 2`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `h4.trans hlow`.
-/
theorem tied_regularization_asymptotic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ δ > (0 : ℝ), ∀ᶠ t' in 𝓝[>] (0 : ℝ), ∀ a, ∀ t : Fin D.n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, -(δ * ‖v‖ ^ 2) ≤ levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hT δ hδ
  have hC := fun a => exists_deriv_bound D M S'.B.toPotentialCharts a
  choose C hC using hC
  set C0 : ℝ := ∑ a, |C a| with hC0
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg fun a _ => abs_nonneg _
  have hCle : ∀ a, C a ≤ C0 := fun a =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) (Finset.mem_univ a))
  set Cη : ℝ := max S'.Cη 0 with hCη
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 4 * Cη * S'.e1 t * C0 ^ 2 < δ := by
    have h0 : Tendsto (fun t => 4 * Cη * S'.e1 t * C0 ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Cη * 0 * C0 ^ 2)) :=
      ((hT.e1_tendsto_zero.const_mul (4 * Cη)).mul_const (C0 ^ 2))
    rw [mul_zero, zero_mul] at h0
    exact (tendsto_order.1 h0).2 δ hδ
  filter_upwards [self_mem_nhdsWithin, hT.compare, eventually_closedBall_subset D M S'.B.toPotentialCharts, hsmall]
    with t' ht' hcmp hball hsm
  have hε : 0 < S'.e1 t' := lt_of_lt_of_le ht' (S'.e1_ge t' ht')
  obtain ⟨hsmooth, hlev⟩ := GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc D.n M.atlas S'.B S'.ρ S'.η S'.Cη t'
    (S'.e1 t') S'.cutoff ht' hε hball hcmp
  intro a t ht v
  have htb : t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  obtain ⟨k, hk, hbd⟩ := hC a t (mem_closedBall_zero_iff.2 ht)
  have hl : levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v =
      levi (S'.B.toPotentialCharts.chartFun (S'.bregWeight t') k) (S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ t)))
        (fderiv ℂ (fun s => S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ s))) t v) :=
    levi_chartFun_gen D M S'.B.toPotentialCharts S'.ref S'.th_ref hsmooth ((D.chart a).analytic t htb)
      (eventually_mem D a htb) k (GroundTheory.Heights₂.Heights.Regular.PotentialCharts.mid_subset_source _ k hk) v
  rw [hl]
  set X := fderiv ℂ (fun s => S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ s))) t v with hX
  have hlow := hlev k _ hk X
  have hXn : ‖X‖ ≤ C0 * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbd.trans (hCle a)) (norm_nonneg _))
  have hX2 : ‖X‖ ^ 2 ≤ C0 ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hXn 2
  have hCη1 : S'.Cη ≤ Cη := le_max_left _ _
  have hCη0 : 0 ≤ Cη := le_max_right _ _
  have h1 : 4 * S'.Cη * S'.e1 t' * ‖X‖ ^ 2 ≤ 4 * Cη * S'.e1 t' * ‖X‖ ^ 2 := by
    gcongr
  have h2 : 4 * Cη * S'.e1 t' * ‖X‖ ^ 2 ≤ 4 * Cη * S'.e1 t' * (C0 ^ 2 * ‖v‖ ^ 2) := by
    gcongr
  have h3 : 4 * Cη * S'.e1 t' * (C0 ^ 2 * ‖v‖ ^ 2) ≤ δ * ‖v‖ ^ 2 := by
    rw [← _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_right hsm.le (sq_nonneg _)
  have h4 : -(δ * ‖v‖ ^ 2) ≤ -(4 * S'.Cη * S'.e1 t') * ‖X‖ ^ 2 := by
    nlinarith
  exact h4.trans hlow

end LevelTowerAlt
