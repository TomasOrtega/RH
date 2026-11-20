import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Real

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Unfold `circleIntegral`. Rewrite using `[← ContinuousLinearMap.intervalIntegral_comp_comm L hf.out]`. Use `congr 1`. Use function extensionality and compare the values at `θ`. Conclude with `L.map_smul _ _`.
-/
theorem clm_circleIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) : L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  unfold circleIntegral
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hf.out]
  congr 1
  funext θ
  exact L.map_smul _ _

/- English proof (translation)
Introduce `X _ _ U F hU hF hd`. Establish `hG : Continuous (fun p : U × X => F p.1.1 p.2)` using `hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) (fun p => ⟨p.1.2, mem_univ _⟩)`. Set `K : C(U, C(X, ℂ))` to `(⟨_, hG⟩ : C(U × X, ℂ)).curry`. Set `Φ : ℂ → C(X, ℂ)` to `fun z => if h : z ∈ U then K ⟨z, h⟩ else 0`. Establish `hΦ : ∀ z ∈ U, ∀ x, Φ z x = F z x`.

Introduce `z hz x`. Simplify using `[Φ, K, hz]`. Establish `hc : ContinuousOn Φ U`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `K.continuous using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Use `show Φ z = K z`. Simplify using `only [Φ, dif_pos z.2, Subtype.coe_eta]`. Use `⟨Φ, ?_, hΦ⟩` and prove the remaining obligations. Introduce `w hw`.

Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Choose the witnesses or unpack the hypotheses as in `⟨R, hR0, hRU⟩ : ∃ R > 0, closedBall w R ⊆ U := by`. Take `⟨ε, hε, hεU⟩` from `Metric.isOpen_iff.mp hU w hw`. Conclude with `⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩`. Set `R' : NNReal` to `⟨R, hR0.le⟩`.

Establish `hsph : sphere w R ⊆ U` using `sphere_subset_closedBall.trans hRU`. Establish `hint : CircleIntegrable Φ w R'` using `(hc.mono hsph).circleIntegrable hR0.le`. Establish `hps` using `hasFPowerSeriesOn_cauchy_integral hint (show (0 : NNReal) < R' from hR0)`. Establish `heq : Φ =ᶠ[𝓝 w] (fun v => (2 * ↑π * I)⁻¹ • ∮ z in C(w, ↑R'), (z - v)⁻¹ • Φ z)` using `by filter_upwards [ball_mem_nhds w hR0] with v hv`. Use extensionality with `x`.

Use `show Φ v x = ((2 * ↑π * I)⁻¹ • ∮ z in C(w, R), (z - v)⁻¹ • Φ z) x`. Establish `ha : ContinuousOn (fun z : ℂ => (z - v)⁻¹) (sphere w R)`. Apply `ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)` to reduce the goal to its premises. Introduce `z hz h`. Establish `hzv : z = v` using `sub_eq_zero.mp h`.

Substitute `hzv` using the available equality. Rewrite `hz` using `[mem_sphere]`. Rewrite `hv` using `[mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcv : ContinuousOn (fun z => (z - v)⁻¹ • Φ z) (sphere w R)` using `ContinuousOn.smul (f := fun z : ℂ => (z - v)⁻¹) (g := Φ) ha (hc.mono hsph)`.

Establish `h1` using `clm_circleIntegral (ContinuousMap.evalCLM ℂ x) (hcv.circleIntegrable hR0.le)`. Simplify using `only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] at h1`. Establish `h2 : (∮ z in C(w, R), (z - v)⁻¹ • Φ z) x = ∮ z in C(w, R), (z - v)⁻¹ • F z x`. Rewrite using `[h1]`. Apply `circleIntegral.integral_congr hR0.le` to reduce the goal to its premises.

Introduce `z hz`. Simplify using `only`. Rewrite using `[hΦ z (hsph hz) x]`. Establish `h3` using `((hd x).mono hRU).circleIntegral_sub_inv_smul hv`. Rewrite using `[ContinuousMap.smul_apply, h2, h3, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul, hΦ v (hRU (ball_subset_closedBall hv))]`.

Conclude with `hps.analyticAt.differentiableAt.congr_of_eventuallyEq heq`.
-/
theorem banachHol : BanachHol := by
  intro X _ _ U F hU hF hd
  have hG : Continuous (fun p : U × X => F p.1.1 p.2) :=
    hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  let K : C(U, C(X, ℂ)) := (⟨_, hG⟩ : C(U × X, ℂ)).curry
  classical
  let Φ : ℂ → C(X, ℂ) := fun z => if h : z ∈ U then K ⟨z, h⟩ else 0
  have hΦ : ∀ z ∈ U, ∀ x, Φ z x = F z x := by
    intro z hz x
    simp [Φ, K, hz]
  have hc : ContinuousOn Φ U := by
    rw [continuousOn_iff_continuous_restrict]
    convert K.continuous using 1
    funext z
    show Φ z = K z
    simp only [Φ, dif_pos z.2, Subtype.coe_eta]
  refine ⟨Φ, ?_, hΦ⟩
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R, hR0, hRU⟩ : ∃ R > 0, closedBall w R ⊆ U := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU w hw
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  let R' : NNReal := ⟨R, hR0.le⟩
  have hsph : sphere w R ⊆ U := sphere_subset_closedBall.trans hRU
  have hint : CircleIntegrable Φ w R' := (hc.mono hsph).circleIntegrable hR0.le
  have hps := hasFPowerSeriesOn_cauchy_integral hint (show (0 : NNReal) < R' from hR0)
  have heq : Φ =ᶠ[𝓝 w] (fun v => (2 * ↑π * I)⁻¹ • ∮ z in C(w, ↑R'), (z - v)⁻¹ • Φ z) := by
    filter_upwards [ball_mem_nhds w hR0] with v hv
    ext x
    show Φ v x = ((2 * ↑π * I)⁻¹ • ∮ z in C(w, R), (z - v)⁻¹ • Φ z) x
    have ha : ContinuousOn (fun z : ℂ => (z - v)⁻¹) (sphere w R) := by
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz h
      have hzv : z = v := sub_eq_zero.mp h
      subst hzv
      rw [mem_sphere] at hz
      rw [mem_ball] at hv
      linarith
    have hcv : ContinuousOn (fun z => (z - v)⁻¹ • Φ z) (sphere w R) :=
      ContinuousOn.smul (f := fun z : ℂ => (z - v)⁻¹) (g := Φ) ha (hc.mono hsph)
    have h1 := clm_circleIntegral (ContinuousMap.evalCLM ℂ x) (hcv.circleIntegrable hR0.le)
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] at h1
    have h2 : (∮ z in C(w, R), (z - v)⁻¹ • Φ z) x = ∮ z in C(w, R), (z - v)⁻¹ • F z x := by
      rw [h1]
      apply circleIntegral.integral_congr hR0.le
      intro z hz
      simp only
      rw [hΦ z (hsph hz) x]
    have h3 := ((hd x).mono hRU).circleIntegral_sub_inv_smul hv
    rw [ContinuousMap.smul_apply, h2, h3, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul,
      hΦ v (hRU (ball_subset_closedBall hv))]
  exact hps.analyticAt.differentiableAt.congr_of_eventuallyEq heq

/- English proof (translation)
Introduce `X _ _ U s₀ F hU hs hF hd h0`. Establish `hU0 : U ∈ 𝓝 s₀` using `hU.mem_nhds hs`. Use `⟨?_, fun x => (differentiableOn_dslope hU0).mpr (hd x)⟩` and prove the remaining obligations. Introduce and unpack `⟨z₀, x₀⟩ hp`. Establish `hz₀ : z₀ ∈ U` using `hp.1`.

Take `⟨K, hKc, hKn⟩` from `exists_compact_mem_nhds x₀`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc`. Establish `hF' : ContinuousOn (fun y : ℂ × K => F y.1 y.2) (U ×ˢ univ)` using `hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn (fun y hy => ⟨hy.1, mem_univ _⟩)`. Take `⟨Φ, hΦd, hΦ⟩` from `banachHol (↥K) U (fun z (y : ↥K) => F z y) hU hF' (fun y => hd y)`. Establish `hD : ContinuousOn (dslope Φ s₀) U` using `((differentiableOn_dslope hU0).mpr hΦd).continuousOn`.

Establish `hval : ∀ z ∈ U, ∀ y : K, dslope Φ s₀ z y = dslope (fun z => F z y) s₀ z`. Introduce `z hz y`. Establish `heqon : EqOn (fun z => F z y) ((ContinuousMap.evalCLM ℂ y) ∘ Φ) U`. Introduce `u hu`. Simplify using `[hΦ u hu y]`.

Rewrite using `[show dslope Φ s₀ z y = ContinuousMap.evalCLM ℂ y (dslope Φ s₀ z) from rfl, ← ContinuousLinearMap.dslope_comp _ _ _ _ (fun _ => (hΦd s₀ hs).differentiableAt hU0)]`. Distinguish the cases in `hzs : z = s₀`. Rewrite using `[hzs, dslope_same, dslope_same]`. Conclude with `(Filter.eventuallyEq_of_mem hU0 heqon).deriv_eq.symm`. Rewrite using `[dslope_of_ne _ hzs, dslope_of_ne _ hzs]`.

Simplify using `[slope_def_field, hΦ z hz y, hΦ s₀ hs y]`. Establish `hcont : ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ K)`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `hDr : Continuous (fun q : ↥(U ×ˢ K) => dslope Φ s₀ q.1.1)` using `hD.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun q => q.2.1)`. Establish `hKr : Continuous (fun q : ↥(U ×ˢ K) => (⟨q.1.2, q.2.2⟩ : K))` using `(continuous_snd.comp continuous_subtype_val).subtype_mk _`.

Use `continuous_eval.comp (hDr.prodMk hKr) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `q`. Conclude with `(hval q.1.1 q.2.1 ⟨q.1.2, q.2.2⟩).symm`. Establish `hmem : U ×ˢ K ∈ 𝓝[U ×ˢ univ] (z₀, x₀)`. Establish `hsub : (U ×ˢ univ) ∩ (univ ×ˢ K) ⊆ U ×ˢ K` using `fun q hq => ⟨hq.1.1, hq.2.2⟩`.

Conclude with `mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds univ_mem hKn)) hsub`. Conclude with `(hcont (z₀, x₀) ⟨hz₀, mem_of_mem_nhds hKn⟩).mono_of_mem_nhdsWithin hmem`.
-/
theorem dslopeFam : DslopeFam := by
  intro X _ _ U s₀ F hU hs hF hd h0
  have hU0 : U ∈ 𝓝 s₀ := hU.mem_nhds hs
  refine ⟨?_, fun x => (differentiableOn_dslope hU0).mpr (hd x)⟩
  rintro ⟨z₀, x₀⟩ hp
  have hz₀ : z₀ ∈ U := hp.1
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x₀
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hF' : ContinuousOn (fun y : ℂ × K => F y.1 y.2) (U ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := banachHol (↥K) U (fun z (y : ↥K) => F z y) hU hF' (fun y => hd y)
  have hD : ContinuousOn (dslope Φ s₀) U := ((differentiableOn_dslope hU0).mpr hΦd).continuousOn
  have hval : ∀ z ∈ U, ∀ y : K, dslope Φ s₀ z y = dslope (fun z => F z y) s₀ z := by
    intro z hz y
    have heqon : EqOn (fun z => F z y) ((ContinuousMap.evalCLM ℂ y) ∘ Φ) U := by
      intro u hu
      simp [hΦ u hu y]
    rw [show dslope Φ s₀ z y = ContinuousMap.evalCLM ℂ y (dslope Φ s₀ z) from rfl,
      ← ContinuousLinearMap.dslope_comp _ _ _ _ (fun _ => (hΦd s₀ hs).differentiableAt hU0)]
    by_cases hzs : z = s₀
    · rw [hzs, dslope_same, dslope_same]
      exact (Filter.eventuallyEq_of_mem hU0 heqon).deriv_eq.symm
    · rw [dslope_of_ne _ hzs, dslope_of_ne _ hzs]
      simp [slope_def_field, hΦ z hz y, hΦ s₀ hs y]
  have hcont : ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ K) := by
    rw [continuousOn_iff_continuous_restrict]
    have hDr : Continuous (fun q : ↥(U ×ˢ K) => dslope Φ s₀ q.1.1) :=
      hD.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun q => q.2.1)
    have hKr : Continuous (fun q : ↥(U ×ˢ K) => (⟨q.1.2, q.2.2⟩ : K)) :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    convert continuous_eval.comp (hDr.prodMk hKr) using 1
    funext q
    exact (hval q.1.1 q.2.1 ⟨q.1.2, q.2.2⟩).symm
  have hmem : U ×ˢ K ∈ 𝓝[U ×ˢ univ] (z₀, x₀) := by
    have hsub : (U ×ˢ univ) ∩ (univ ×ˢ K) ⊆ U ×ˢ K := fun q hq => ⟨hq.1.1, hq.2.2⟩
    exact mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds univ_mem hKn)) hsub
  exact (hcont (z₀, x₀) ⟨hz₀, mem_of_mem_nhds hKn⟩).mono_of_mem_nhdsWithin hmem

end PositivityTheory.Rg.Sw.AbsSt
