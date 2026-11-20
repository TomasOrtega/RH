import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartMollifiedBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
set_option maxSynthPendingDepth 1

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
open ReciprocityTheory.AnForm.M.PLAux (analyticAt_compat)

section Charts

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

/- English proof (translation)
Establish `h` using `analyticAt_compat (P.compat k) j ((A.chart j).map_target hy) hk`. Rewrite `h` using `[(A.chart j).right_inv hy]`. Then use the resulting hypothesis.
-/
theorem analyticAt_transition (P : PotentialCharts A) (j : Fin A.n) (k : Fin P.N) {y : Fin D → ℂ}
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (P.chart k).source) :
    AnalyticAt ℂ (P.chart k ∘ (A.chart j).symm) y := by
  have h := analyticAt_compat (P.compat k) j ((A.chart j).map_target hy) hk
  rwa [(A.chart j).right_inv hy] at h

/- English proof (translation)
Establish `hg` using `analyticAt_transition P j k hy hk`. Take `⟨W, hWo, hpW, G, hG, hEq⟩` from `P.q_th k x _ ⟨hθ, hk⟩`. Establish `hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 ((A.chart j).symm y)` using `((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hθ⟩, hk⟩`. Establish `hev : (fun z => P.th.φ x z + f z) ∘ (A.chart j).symm =ᶠ[𝓝 y] fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y' + (-1) * (G ((A.chart j).symm y')).re` using `by filter_upwards [((A.chart j).continuousAt_symm hy).preimage_mem_nhds hN] with y' hy'`. Establish `h1` using `hEq _ hy'`.

Simplify using `only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y` using `hG j y ⟨hy, hpW⟩`. Establish `hcf' : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart j).symm) y)` using `hcf`. Establish `hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y` using `hcf'.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)`.

Establish `hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart j).symm y')).re) y`. Use `(Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `h0 : levi (fun y' => (G ((A.chart j).symm y')).re) y w = 0` using `levi_re_analytic hGa w`. Use `⟨(hcg.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq hev, ?_⟩` and prove the remaining obligations.

Rewrite using `[levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf']`. Simplify using the standard rewrite rules.
-/
theorem levi_th_add_chart (P : PotentialCharts A) (f : X → ℝ) (x : X) (j : Fin A.n) (k : Fin P.N)
    {y : Fin D → ℂ} (w : Fin D → ℂ) (hy : y ∈ (A.chart j).target)
    (hθ : (A.chart j).symm y ∈ P.th.U x) (hk : (A.chart j).symm y ∈ (P.chart k).source)
    (hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y))) :
    ContDiffAt ℝ 2 ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y ∧
      levi ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y w =
        levi (P.chartFun f k) (P.chart k ((A.chart j).symm y))
          (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
  have hg := analyticAt_transition P j k hy hk
  obtain ⟨W, hWo, hpW, G, hG, hEq⟩ := P.q_th k x _ ⟨hθ, hk⟩
  have hN : W ∩ P.th.U x ∩ (P.chart k).source ∈ 𝓝 ((A.chart j).symm y) :=
    ((hWo.inter (P.th.isOpen_U x)).inter (P.chart k).open_source).mem_nhds ⟨⟨hpW, hθ⟩, hk⟩
  have hev : (fun z => P.th.φ x z + f z) ∘ (A.chart j).symm =ᶠ[𝓝 y]
      fun y' => (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y' +
        (-1) * (G ((A.chart j).symm y')).re := by
    filter_upwards [((A.chart j).continuousAt_symm hy).preimage_mem_nhds hN] with y' hy'
    have h1 := hEq _ hy'
    simp only [Function.comp, PotentialCharts.chartFun, (P.chart k).left_inv hy'.2]
    linarith
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hcf' : ContDiffAt ℝ 2 (P.chartFun f k) ((P.chart k ∘ (A.chart j).symm) y) := hcf
  have hcg : ContDiffAt ℝ 2 (P.chartFun f k ∘ (P.chart k ∘ (A.chart j).symm)) y :=
    hcf'.comp y ((hg.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hre : ContDiffAt ℝ 2 (fun y' => (G ((A.chart j).symm y')).re) y := by
    have := (Complex.reCLM.contDiff (𝕜 := ℝ) (n := 2)).contDiffAt.comp y
      ((hGa.contDiffAt (n := 2)).restrict_scalars ℝ)
    simpa [Function.comp_def] using this
  have h0 : levi (fun y' => (G ((A.chart j).symm y')).re) y w = 0 := levi_re_analytic hGa w
  refine ⟨(hcg.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq hev, ?_⟩
  rw [levi_congr hev w, levi_add_smul (-1) hcg hre w, h0, levi_comp w hg hcf']
  simp

/- English proof (translation)
Introduce `x j y hy w`. Establish `hyt : y ∈ (A.chart j).target` using `hy.1`. Establish `hθ : (A.chart j).symm y ∈ R.th.U x` using `hy.2.1.1`. Establish `hY : (A.chart j).symm y ∈ R.Yo` using `hy.2.2`. Take `⟨k, hk⟩` from `R.cover ((A.chart j).symm y)`.

Establish `hks` using `R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)`. Establish `hξ : R.chart k ((A.chart j).symm y) ∈ (R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)` using `⟨(R.chart k).map_source hks, (R.mem_Yo k _ hks).1 hY⟩`. Establish `hUo : IsOpen ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k))` using `(R.chart k).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)`. Establish `hC2 : ContDiffOn ℝ 2 (R.u k) ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k))` using `fun ξ hξ => (RegChartData.contDiffAt_u R k hξ).contDiffWithinAt`. Establish `hL` using `((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (R.u_psh k)).2`.

Establish `hcf : ContDiffAt ℝ 2 (R.chartFun R.ph k) (R.chart k ((A.chart j).symm y))` using `RegChartData.contDiffAt_u R k hξ`. Establish `h` using `(levi_th_add_chart R.toPotentialCharts R.ph x j k w hyt hθ hks hcf).2`. Express the relevant statement in the definitionally equal form `0 ≤ levi ((fun z => R.th.φ x z + R.ph z) ∘ (A.chart j).symm) y w`. Rewrite using `[h]`. Conclude with `hL _ hξ _`.
-/
theorem isPshOn_th_ph (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) :
    ReciprocityTheory.AnForm.P.IsPshOn A R.Yo (R.th + LocPot.ofFun R.ph) := by
  intro x j y hy w
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ R.th.U x := hy.2.1.1
  have hY : (A.chart j).symm y ∈ R.Yo := hy.2.2
  obtain ⟨k, hk⟩ := R.cover ((A.chart j).symm y)
  have hks := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hξ : R.chart k ((A.chart j).symm y) ∈
      (R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k) :=
    ⟨(R.chart k).map_source hks, (R.mem_Yo k _ hks).1 hY⟩
  have hUo : IsOpen ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    (R.chart k).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (R.u k) ((R.chart k).target \ ReciprocityTheory.AnForm.A.coordDiv (R.S k)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u R k hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (R.u_psh k)).2
  have hcf : ContDiffAt ℝ 2 (R.chartFun R.ph k) (R.chart k ((A.chart j).symm y)) :=
    RegChartData.contDiffAt_u R k hξ
  have h := (levi_th_add_chart R.toPotentialCharts R.ph x j k w hyt hθ hks hcf).2
  change 0 ≤ levi ((fun z => R.th.φ x z + R.ph z) ∘ (A.chart j).symm) y w
  rw [h]
  exact hL _ hξ _

/- English proof (translation)
Establish `hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closure (P.mid k), ∀ x, p ∈ Θ.U x → ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k p) v` using `fun k => exists_levi_lower hΘ hpos (P.compat k) isClosed_closure.isCompact (P.closure_mid k)`. Use `choose c hc0 hc using hc`. Use `⟨c, hc0, fun f a ε hf hε hlev hac x j y hy w => ?_⟩` and prove the remaining obligations. Establish `hyt : y ∈ (A.chart j).target` using `hy.1`. Establish `hθ : (A.chart j).symm y ∈ P.th.U x` using `hy.2.1.1`.

Establish `hΘx : (A.chart j).symm y ∈ Θ.U x` using `hy.2.2`. Establish `hpA : (A.chart j).symm y ∈ (A.chart j).source` using `(A.chart j).map_target hyt`. Take `⟨k, hk⟩` from `P.cover ((A.chart j).symm y)`. Establish `hkm` using `P.inner_subset_mid k hk`. Establish `hks` using `P.mid_subset_source k hkm`.

Establish `hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y))`. Establish `hq : ContDiffAt ℝ 2 (P.q k) (P.chart k ((A.chart j).symm y))` using `((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)`. Conclude with `hq.add (contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ _) hks)`. Take `⟨hF, hFl⟩` from `levi_th_add_chart P f x j k w hyt hθ hks hcf`. Establish `hG : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y`.

Use `contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (compat_chart A j) hΘx hpA` as an intermediate fact. Rewrite `this` using `[(A.chart j).right_inv hyt]`. Then use the resulting hypothesis. Establish `hg` using `analyticAt_transition P j k hyt hks`. Establish `hGl : levi (Θ.φ x ∘ (A.chart j).symm) y w = levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k ((A.chart j).symm y)) (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w)`. Establish `hev` using `eventuallyEq_comp_chart (Θ.φ x) (P.chart k) (A.chart j) hyt hks`.

Establish `hcd : ContDiffAt ℝ 2 (Θ.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart j).symm) y)` using `contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (P.compat k) hΘx hks`. Rewrite using `[levi_congr hev w, levi_comp w hg hcd]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `0 ≤ levi (fun y' => ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y' + ε * (Θ.φ x ∘ (A.chart j).symm) y') y w`. Rewrite using `[levi_add_smul ε hF hG w, hFl, hGl]`.

Use `set v := fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w`. Establish `h1` using `hlev k _ hkm v`. Establish `h2` using `hc k _ (subset_closure hkm) x hΘx v`. Establish `h3` using `mul_le_mul_of_nonneg_left h2 hε`. Establish `h4` using `mul_le_mul_of_nonneg_right (hac k) (sq_nonneg ‖v‖)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_isPsh_of_chart_bound [CompactSpace X] (P : PotentialCharts A) (Θ : LocPot X)
    (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    ∃ c : Fin P.N → ℝ, (∀ k, 0 < c k) ∧ ∀ (f : X → ℝ) (a ε : ℝ), A.Smooth f → 0 ≤ ε →
      (∀ k : Fin P.N, ∀ x ∈ P.mid k, ∀ w : Fin D → ℂ,
        -a * ‖w‖ ^ 2 ≤ levi (P.chartFun f k) (P.chart k x) w) →
      (∀ k, a ≤ ε * c k) → IsPsh A (P.th + LocPot.ofFun f + Θ.rsmul ε) := by
  have hc : ∀ k : Fin P.N, ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closure (P.mid k), ∀ x, p ∈ Θ.U x →
      ∀ v : Fin D → ℂ, c * ‖v‖ ^ 2 ≤ levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k p) v := fun k =>
    exists_levi_lower hΘ hpos (P.compat k) isClosed_closure.isCompact (P.closure_mid k)
  choose c hc0 hc using hc
  refine ⟨c, hc0, fun f a ε hf hε hlev hac x j y hy w => ?_⟩
  have hyt : y ∈ (A.chart j).target := hy.1
  have hθ : (A.chart j).symm y ∈ P.th.U x := hy.2.1.1
  have hΘx : (A.chart j).symm y ∈ Θ.U x := hy.2.2
  have hpA : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
  obtain ⟨k, hk⟩ := P.cover ((A.chart j).symm y)
  have hkm := P.inner_subset_mid k hk
  have hks := P.mid_subset_source k hkm
  have hcf : ContDiffAt ℝ 2 (P.chartFun f k) (P.chart k ((A.chart j).symm y)) := by
    have hq : ContDiffAt ℝ 2 (P.q k) (P.chart k ((A.chart j).symm y)) :=
      ((P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds
        ((P.chart k).map_source hks))).of_le (WithTop.coe_le_coe.2 le_top)
    exact hq.add (contDiffAt_comp_symm isOpen_univ hf (P.compat k) (Set.mem_univ _) hks)
  obtain ⟨hF, hFl⟩ := levi_th_add_chart P f x j k w hyt hθ hks hcf
  have hG : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have := contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (compat_chart A j) hΘx hpA
    rwa [(A.chart j).right_inv hyt] at this
  have hg := analyticAt_transition P j k hyt hks
  have hGl : levi (Θ.φ x ∘ (A.chart j).symm) y w =
      levi (Θ.φ x ∘ (P.chart k).symm) (P.chart k ((A.chart j).symm y))
        (fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w) := by
    have hev := eventuallyEq_comp_chart (Θ.φ x) (P.chart k) (A.chart j) hyt hks
    have hcd : ContDiffAt ℝ 2 (Θ.φ x ∘ (P.chart k).symm) ((P.chart k ∘ (A.chart j).symm) y) :=
      contDiffAt_comp_symm (Θ.isOpen_U x) (hΘ.1 x) (P.compat k) hΘx hks
    rw [levi_congr hev w, levi_comp w hg hcd]
    rfl
  change 0 ≤ levi (fun y' => ((fun z => P.th.φ x z + f z) ∘ (A.chart j).symm) y' +
    ε * (Θ.φ x ∘ (A.chart j).symm) y') y w
  rw [levi_add_smul ε hF hG w, hFl, hGl]
  set v := fderiv ℂ (P.chart k ∘ (A.chart j).symm) y w
  have h1 := hlev k _ hkm v
  have h2 := hc k _ (subset_closure hkm) x hΘx v
  have h3 := mul_le_mul_of_nonneg_left h2 hε
  have h4 := mul_le_mul_of_nonneg_right (hac k) (sq_nonneg ‖v‖)
  nlinarith

end Charts

/- English proof (translation)
Introduce `K _ ι _ P n M Xo B S Θ hS hΘ hpos`. Take `⟨C₀, t₀, ht₀, hb⟩` from `GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof M.Xc n M.atlas S.R S.ρ`. Use `⟨isPshOn_th_ph S.R, ⟨C₀ + 1, ?_⟩, fun ε hε => ?_⟩` and prove the remaining obligations. Use `filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀), hS.K_tendsto.eventually_ge_atTop 0, hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he`. Establish `ht0 : (0 : ℝ) < t` using `ht`.

Establish `hε0 : 0 ≤ S.e1 t` using `ht0.le.trans (S.e1_ge t ht0)`. Use `⟨hsm.1, fun x hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `S.R.cover x`. Establish `hkm` using `S.R.inner_subset_mid k hk`. Establish `h1` using `((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx`.

Establish `h2` using `GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue S.R.toPotentialCharts (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm`. Establish `h3 : S.regWeight t x = S.R.glue (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x` using `rfl`. Establish `hη` using `S.cutoff.eq_zero k x hk`. Simplify using `only [hη, mul_zero, add_zero] at h2`. Rewrite using `[h3]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg` using `GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.glue_le S.R.toPotentialCharts (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 (c := C₀) (x := x) fun j hj => by`. Establish `h1` using `((hb t ht0 htt).2 (S.K t) hK j x hj).2.1`. Establish `h2` using `mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t) (S.cutoff.bounds j x hj).2`. Use `show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ C₀`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : S.regWeight t x = S.R.glue (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x` using `rfl`. Rewrite using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨c, hc0, hc⟩` from `exists_isPsh_of_chart_bound S.R.toPotentialCharts Θ hΘ hpos`.

Establish `hlim : Tendsto (fun t => 4 * S.Cη * S.e1 t) (𝓝[>] 0) (𝓝 0)`. Simplify using `using hS.e1_tendsto_zero.const_mul (4 * S.Cη)`. Establish `hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, 4 * S.Cη * S.e1 t ≤ ε * c k` using `Filter.eventually_all.2 fun k => hlim.eventually (eventually_le_nhds (mul_pos hε (hc0 k)))`. Use `filter_upwards [S.eventually_chartLevi hS, hall] with t ht hle`. Conclude with `hc (S.regWeight t) (4 * S.Cη * S.e1 t) ε ht.1 hε.le ht.2 hle`.
-/
theorem tied_regularisation_weak : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B) (Θ : LocPot M.Xc), S.IsTied → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → ReciprocityTheory.AnForm.P.IsPshOn M.atlas S.R.Yo (S.R.th + LocPot.ofFun S.R.ph) ∧ (∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧ ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x ∧ S.regWeight t x ≤ C) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), IsPsh M.atlas (S.R.th + LocPot.ofFun (S.regWeight t) + Θ.rsmul ε) := by
  intro K _ ι _ P n M Xo B S Θ hS hΘ hpos
  obtain ⟨C₀, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  refine ⟨isPshOn_th_ph S.R, ⟨C₀ + 1, ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀),
      hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨hsm.1, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := S.R.cover x
      have hkm := S.R.inner_subset_mid k hk
      have h1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
      have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      have hη := S.cutoff.eq_zero k x hk
      simp only [hη, mul_zero, add_zero] at h2
      rw [h3]
      linarith
    · have hg := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.glue_le S.R.toPotentialCharts
        (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 (c := C₀) (x := x)
        fun j hj => by
          have h1 := ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
          have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t)
            (S.cutoff.bounds j x hj).2
          show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ C₀
          linarith
      have h3 : S.regWeight t x = S.R.glue
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := rfl
      rw [h3]
      linarith
  · obtain ⟨c, hc0, hc⟩ := exists_isPsh_of_chart_bound S.R.toPotentialCharts Θ hΘ hpos
    have hlim : Tendsto (fun t => 4 * S.Cη * S.e1 t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hS.e1_tendsto_zero.const_mul (4 * S.Cη)
    have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, 4 * S.Cη * S.e1 t ≤ ε * c k :=
      Filter.eventually_all.2 fun k =>
        hlim.eventually (eventually_le_nhds (mul_pos hε (hc0 k)))
    filter_upwards [S.eventually_chartLevi hS, hall] with t ht hle
    exact hc (S.regWeight t) (4 * S.Cη * S.e1 t) ε ht.1 hε.le ht.2 hle

end GlobalTheory.CompanionTheory.Ar.Giv
