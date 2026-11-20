import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsCompactImageClosureMid
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric Set
open ReciprocityTheory.AnForm.A (Mollifier tmax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular (BoundedPshData RegChartData PotentialCharts regMax_bounds
  continuous_of_atlasSmooth)

/- English proof (translation)
Take `⟨u, hu, hsub⟩` from `mem_nhdsGT_iff_exists_Ioo_subset.1 h`. Conclude with `⟨u, hu, fun t h0 h1 => hsub ⟨h0, h1⟩⟩`.
-/
theorem exists_Ioo_of_eventually_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), p t) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → p t := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun t h0 h1 => hsub ⟨h0, h1⟩⟩

section Bounded

variable {X : Type} [TopologicalSpace X] {D : ℕ} {A : FinHolAtlas D X} (B : BoundedPshData A)
  (ρ : Mollifier D)

/- English proof (translation)
Simplify using `only [BoundedPshData.u, PotentialCharts.chartFun, (B.chart j).left_inv (B.mid_subset_source j hx)]`.
-/
theorem boundedPsh_u_chart {j : Fin B.N} {x : X} (hx : x ∈ B.mid j) :
    B.u j (B.chart j x) = B.q j (B.chart j x) + B.ph x := by
  simp only [BoundedPshData.u, PotentialCharts.chartFun,
    (B.chart j).left_inv (B.mid_subset_source j hx)]

/- English proof (translation)
The claim follows from `(closedBall_subset_closedBall htδ).trans (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)`.
-/
theorem boundedPsh_ball_subset {δ t : ℝ} (htδ : t ≤ δ)
    (j : Fin B.N) {x : X} (hx : x ∈ closure (B.mid j)) :
    closedBall (B.chart j x) t ⊆ cthickening δ ((B.chart j) '' closure (B.mid j)) :=
  (closedBall_subset_closedBall htδ).trans (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)

/- English proof (translation)
Establish `hz : B.chart j x ∈ shrink (B.chart j).target t` using `(boundedPsh_ball_subset B htδ j (subset_closure hx)).trans (hδ j)`. Establish `hmol` using `ReciprocityTheory.AnForm.A.mollify_thm D ρ (B.chart j).target (B.u j) (B.chart j).open_target (B.u_psh j)`. Use `((hmol.1 t ht).2.2.2 _ hz).1` as an intermediate fact. Rewrite `this` using `[boundedPsh_u_chart B hx]`. Simplify using `only [BoundedPshData.phReg, BoundedPshData.smoothed]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem boundedPsh_le_phReg {δ t : ℝ}
    (hδ : ∀ j, cthickening δ ((B.chart j) '' closure (B.mid j)) ⊆ (B.chart j).target)
    (ht : 0 < t) (htδ : t ≤ δ) (j : Fin B.N) {x : X} (hx : x ∈ B.mid j) :
    B.ph x ≤ B.phReg ρ t j x := by
  have hz : B.chart j x ∈ shrink (B.chart j).target t :=
    (boundedPsh_ball_subset B htδ j (subset_closure hx)).trans (hδ j)
  have hmol := ReciprocityTheory.AnForm.A.mollify_thm D ρ (B.chart j).target (B.u j) (B.chart j).open_target
    (B.u_psh j)
  have := ((hmol.1 t ht).2.2.2 _ hz).1
  rw [boundedPsh_u_chart B hx] at this
  simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
  linarith

/- English proof (translation)
Establish `hz : B.chart j x ∈ shrink (B.chart j).target t` using `(boundedPsh_ball_subset B htδ j (subset_closure hx)).trans (hδ j)`. Establish `hmol` using `ReciprocityTheory.AnForm.A.mollify_thm D ρ (B.chart j).target (B.u j) (B.chart j).open_target (B.u_psh j)`. Establish `e1` using `((hmol.1 t ht).2.2.2 _ hz).2`. Establish `e2 : ReciprocityTheory.AnForm.A.polyMax (B.u j) (B.chart j x) t ≤ Q + Cb`. Unfold `ReciprocityTheory.AnForm.A.polyMax`.

Apply `csSup_le ((nonempty_closedBall.2 ht.le).image _)` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `f1` using `hQ j y (boundedPsh_ball_subset B htδ j (subset_closure hx) hy)`. Establish `f2` using `hCb ((B.chart j).symm y)`. Establish `f3` using `le_abs_self (B.q j y)`.

Establish `f4` using `le_abs_self (B.ph ((B.chart j).symm y))`. Simplify using `only [BoundedPshData.u, PotentialCharts.chartFun]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3` using `hQ j _ (self_subset_cthickening _ (mem_image_of_mem _ (subset_closure hx)))`. Establish `e4` using `neg_abs_le (B.q j (B.chart j x))`.

Simplify using `only [BoundedPshData.phReg, BoundedPshData.smoothed]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem boundedPsh_phReg_le {δ t Q Cb : ℝ}
    (hδ : ∀ j, cthickening δ ((B.chart j) '' closure (B.mid j)) ⊆ (B.chart j).target)
    (hQ : ∀ j, ∀ y ∈ cthickening δ ((B.chart j) '' closure (B.mid j)), |B.q j y| ≤ Q)
    (hCb : ∀ x, |B.ph x| ≤ Cb) (ht : 0 < t) (htδ : t ≤ δ) (j : Fin B.N) {x : X} (hx : x ∈ B.mid j) :
    B.phReg ρ t j x ≤ 2 * Q + Cb := by
  have hz : B.chart j x ∈ shrink (B.chart j).target t :=
    (boundedPsh_ball_subset B htδ j (subset_closure hx)).trans (hδ j)
  have hmol := ReciprocityTheory.AnForm.A.mollify_thm D ρ (B.chart j).target (B.u j) (B.chart j).open_target
    (B.u_psh j)
  have e1 := ((hmol.1 t ht).2.2.2 _ hz).2
  have e2 : ReciprocityTheory.AnForm.A.polyMax (B.u j) (B.chart j x) t ≤ Q + Cb := by
    unfold ReciprocityTheory.AnForm.A.polyMax
    apply csSup_le ((nonempty_closedBall.2 ht.le).image _)
    rintro _ ⟨y, hy, rfl⟩
    have f1 := hQ j y (boundedPsh_ball_subset B htδ j (subset_closure hx) hy)
    have f2 := hCb ((B.chart j).symm y)
    have f3 := le_abs_self (B.q j y)
    have f4 := le_abs_self (B.ph ((B.chart j).symm y))
    simp only [BoundedPshData.u, PotentialCharts.chartFun]
    linarith
  have e3 := hQ j _ (self_subset_cthickening _ (mem_image_of_mem _ (subset_closure hx)))
  have e4 := neg_abs_le (B.q j (B.chart j x))
  simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
  linarith

/- English proof (translation)
Establish `hmol` using `ReciprocityTheory.AnForm.A.mollify_thm D ρ (B.chart j).target (B.u j) (B.chart j).open_target (B.u_psh j)`. Use `(hmol.2 _ ((B.chart j).map_source (B.mid_subset_source j hx))).sub_const (B.q j (B.chart j x))` as an intermediate fact. Rewrite `this` using `[boundedPsh_u_chart B hx, add_sub_cancel_left]`. Conclude with `this`.
-/
theorem boundedPsh_tendsto_phReg (j : Fin B.N) {x : X} (hx : x ∈ B.mid j) :
    Tendsto (fun t => B.phReg ρ t j x) (𝓝[>] 0) (𝓝 (B.ph x)) := by
  have hmol := ReciprocityTheory.AnForm.A.mollify_thm D ρ (B.chart j).target (B.u j) (B.chart j).open_target
    (B.u_psh j)
  have := (hmol.2 _ ((B.chart j).map_source (B.mid_subset_source j hx))).sub_const
    (B.q j (B.chart j x))
  rw [boundedPsh_u_chart B hx, add_sub_cancel_left] at this
  exact this

variable {η : Fin B.N → X → ℝ} {Cη : ℝ} (hη : B.IsCutoffFamily η Cη)
include hη

/- English proof (translation)
Take `⟨j₀, hj₀⟩` from `B.cover x`. Establish `hx₀ : x ∈ B.mid j₀` using `B.inner_subset_mid j₀ hj₀`. Establish `hb` using `regMax_bounds (ι := {j // x ∈ B.mid j}) hε (fun j => B.phReg ρ t j x + 4 * ε * η j x)`. Establish `hle : B.phReg ρ t j₀ x + 4 * ε * η j₀ x ≤ tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε * η j x)` using `Finset.le_sup' (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε * η j x) (Finset.mem_univ ⟨j₀, hx₀⟩)`. Rewrite `hle` using `[hη.eq_zero j₀ x hj₀]`.

Establish `e1` using `boundedPsh_le_phReg B ρ hδ ht htδ j₀ hx₀`. Simplify using `only [BoundedPshData.regularised, PotentialCharts.glue]`. Combine the linear relations using `[hb.1]`.
-/
theorem boundedPsh_le_regularised {δ t ε : ℝ}
    (hδ : ∀ j, cthickening δ ((B.chart j) '' closure (B.mid j)) ⊆ (B.chart j).target)
    (ht : 0 < t) (htδ : t ≤ δ) (hε : 0 < ε) (x : X) :
    B.ph x ≤ B.regularised ρ t ε η x := by
  classical
  obtain ⟨j₀, hj₀⟩ := B.cover x
  have hx₀ : x ∈ B.mid j₀ := B.inner_subset_mid j₀ hj₀
  have hb := regMax_bounds (ι := {j // x ∈ B.mid j}) hε (fun j => B.phReg ρ t j x + 4 * ε * η j x)
  have hle : B.phReg ρ t j₀ x + 4 * ε * η j₀ x ≤
      tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε * η j x) :=
    Finset.le_sup' (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε * η j x)
      (Finset.mem_univ ⟨j₀, hx₀⟩)
  rw [hη.eq_zero j₀ x hj₀] at hle
  have e1 := boundedPsh_le_phReg B ρ hδ ht htδ j₀ hx₀
  simp only [BoundedPshData.regularised, PotentialCharts.glue]
  linarith [hb.1]

/- English proof (translation)
Establish `hb` using `regMax_bounds (ι := {j // x ∈ B.mid j}) hε (fun j => B.phReg ρ t j x + 4 * ε * η j x)`. Establish `hle : tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε * η j x) ≤ Mx` using `Finset.sup'_le _ _ fun j _ => by`. Establish `e1` using `(hη.bounds j.1 x j.2).2`. Establish `e2` using `hM j.1 j.2`. Establish `e3 : 4 * ε * η j x ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by linarith) e1`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [BoundedPshData.regularised, PotentialCharts.glue]`. Combine the linear relations using `[hb.2]`.
-/
theorem boundedPsh_regularised_le {t ε : ℝ} (hε : 0 < ε) (x : X) (Mx : ℝ)
    (hM : ∀ j, x ∈ B.mid j → B.phReg ρ t j x ≤ Mx) :
    B.regularised ρ t ε η x ≤ Mx + ε := by
  classical
  have hb := regMax_bounds (ι := {j // x ∈ B.mid j}) hε (fun j => B.phReg ρ t j x + 4 * ε * η j x)
  have hle : tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε * η j x) ≤ Mx :=
    Finset.sup'_le _ _ fun j _ => by
      have e1 := (hη.bounds j.1 x j.2).2
      have e2 := hM j.1 j.2
      have e3 : 4 * ε * η j x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) e1
      linarith
  simp only [BoundedPshData.regularised, PotentialCharts.glue]
  linarith [hb.2]

end Bounded

section Settings

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}

/- English proof (translation)
Take `⟨δ, hδ, hmarg⟩` from `S.B.toPotentialCharts.exists_margin`. Take `⟨Q, hQ⟩` from `S.B.toPotentialCharts.exists_bound_q hmarg`. Take `⟨Cb, hCb⟩` from `S.B.bdd`. Use `⟨|2 * Q + Cb + 1| + |Cb|, ?_⟩` and prove the remaining obligations. Establish `hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ` using `Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2`.

Establish `he : ∀ᶠ t in 𝓝[>] (0 : ℝ), S.e1 t < 1` using `hS.e1_tendsto_zero.eventually (eventually_lt_nhds one_pos)`. Use `filter_upwards [self_mem_nhdsWithin, hδ', he, hS.compare] with t ht htδ he1 hcmp`. Establish `ht' : 0 < t` using `ht`. Establish `hε : 0 < S.e1 t` using `lt_of_lt_of_le ht' (S.e1_ge t ht')`. Use `⟨fun x => ?_, ?_⟩` and prove the remaining obligations.

Establish `e1` using `boundedPsh_le_regularised S.B S.ρ S.cutoff hmarg ht' htδ.le hε x`. Establish `e2` using `boundedPsh_regularised_le S.B S.ρ S.cutoff hε x (2 * Q + Cb) (fun j hj => boundedPsh_phReg_le S.B S.ρ hmarg hQ hCb ht' htδ.le j hj)`. Establish `e3` using `hCb x`. Establish `e4` using `neg_abs_le (S.B.ph x)`. Establish `e5` using `le_abs_self (2 * Q + Cb + 1)`.

Establish `e6` using `le_abs_self Cb`. Establish `e7` using `abs_nonneg (2 * Q + Cb + 1)`. Establish `e8` using `abs_nonneg Cb`. Use `show |S.B.regularised S.ρ t (S.e1 t) S.η x| ≤ _`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith`. Establish `hball : ∀ j, ∀ x ∈ closure (S.B.mid j), closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target` using `fun j x hx => (boundedPsh_ball_subset S.B htδ.le j hx).trans (hmarg j)`. Conclude with `continuous_of_atlasSmooth (GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η S.Cη t (S.e1 t) S.cutoff ht' hε hball hcmp).1`.
-/
theorem BoundedRegularisationSetting.bregWeight_bounds {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ} (S : BoundedRegularisationSetting M Xo a w)
    (hS : S.IsTied) :
    ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, |S.bregWeight t x| ≤ C) ∧ Continuous (S.bregWeight t) := by
  obtain ⟨δ, hδ, hmarg⟩ := S.B.toPotentialCharts.exists_margin
  obtain ⟨Q, hQ⟩ := S.B.toPotentialCharts.exists_bound_q hmarg
  obtain ⟨Cb, hCb⟩ := S.B.bdd
  refine ⟨|2 * Q + Cb + 1| + |Cb|, ?_⟩
  have hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ := Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), S.e1 t < 1 := hS.e1_tendsto_zero.eventually (eventually_lt_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hδ', he, hS.compare] with t ht htδ he1 hcmp
  have ht' : 0 < t := ht
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht' (S.e1_ge t ht')
  refine ⟨fun x => ?_, ?_⟩
  · have e1 := boundedPsh_le_regularised S.B S.ρ S.cutoff hmarg ht' htδ.le hε x
    have e2 := boundedPsh_regularised_le S.B S.ρ S.cutoff hε x (2 * Q + Cb)
      (fun j hj => boundedPsh_phReg_le S.B S.ρ hmarg hQ hCb ht' htδ.le j hj)
    have e3 := hCb x
    have e4 := neg_abs_le (S.B.ph x)
    have e5 := le_abs_self (2 * Q + Cb + 1)
    have e6 := le_abs_self Cb
    have e7 := abs_nonneg (2 * Q + Cb + 1)
    have e8 := abs_nonneg Cb
    show |S.B.regularised S.ρ t (S.e1 t) S.η x| ≤ _
    rw [abs_le]
    constructor <;> linarith
  · have hball : ∀ j, ∀ x ∈ closure (S.B.mid j), closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target :=
      fun j x hx => (boundedPsh_ball_subset S.B htδ.le j hx).trans (hmarg j)
    exact continuous_of_atlasSmooth (GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η
      S.Cη t (S.e1 t) S.cutoff ht' hε hball hcmp).1

/- English proof (translation)
Take `⟨δ, hδ, hmarg⟩` from `S.B.toPotentialCharts.exists_margin`. Establish `hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ` using `Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2`. Rewrite using `[tendsto_order]`. Use `⟨fun a' ha => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, hδ'] with t ht htδ`.

Establish `ht' : 0 < t` using `ht`. Conclude with `ha.trans_le (boundedPsh_le_regularised S.B S.ρ S.cutoff hmarg ht' htδ.le (lt_of_lt_of_le ht' (S.e1_ge t ht')) x)`. Establish `hdpos : 0 < (b - S.B.ph x) / 2` using `by linarith`. Establish `hJ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, x ∈ S.B.mid j → S.B.phReg S.ρ t j x ≤ S.B.ph x + (b - S.B.ph x) / 2`. Rewrite using `[eventually_all]`.

Introduce `j`. Distinguish the cases in `hx : x ∈ S.B.mid j`. Use `filter_upwards [(boundedPsh_tendsto_phReg S.B S.ρ j hx).eventually (eventually_le_nhds (by linarith : S.B.ph x < S.B.ph x + (b - S.B.ph x) / 2))] with t ht _`. Conclude with `ht`. Conclude with `Eventually.of_forall fun _ h => absurd h hx`.

Establish `hE : ∀ᶠ t in 𝓝[>] (0 : ℝ), S.e1 t < (b - S.B.ph x) / 2` using `hS.e1_tendsto_zero.eventually (eventually_lt_nhds hdpos)`. Use `filter_upwards [self_mem_nhdsWithin, hJ, hE] with t ht hJt hEt`. Establish `ht' : 0 < t` using `ht`. Use `boundedPsh_regularised_le S.B S.ρ S.cutoff (lt_of_lt_of_le ht' (S.e1_ge t ht')) x _ hJt` as an intermediate fact. Use `show S.B.regularised S.ρ t (S.e1 t) S.η x < b`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem BoundedRegularisationSetting.tendsto_bregWeight {a : K → ℤ} {w : ((Σ k, ι k) → ℂ) → ℝ} (S : BoundedRegularisationSetting M Xo a w)
    (hS : S.IsTied) (x : M.Xc) :
    Tendsto (fun t => S.bregWeight t x) (𝓝[>] 0) (𝓝 (S.B.ph x)) := by
  obtain ⟨δ, hδ, hmarg⟩ := S.B.toPotentialCharts.exists_margin
  have hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ := Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2
  rw [tendsto_order]
  refine ⟨fun a' ha => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin, hδ'] with t ht htδ
    have ht' : 0 < t := ht
    exact ha.trans_le (boundedPsh_le_regularised S.B S.ρ S.cutoff hmarg ht' htδ.le
      (lt_of_lt_of_le ht' (S.e1_ge t ht')) x)
  · have hdpos : 0 < (b - S.B.ph x) / 2 := by linarith
    have hJ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, x ∈ S.B.mid j →
        S.B.phReg S.ρ t j x ≤ S.B.ph x + (b - S.B.ph x) / 2 := by
      rw [eventually_all]
      intro j
      by_cases hx : x ∈ S.B.mid j
      · filter_upwards [(boundedPsh_tendsto_phReg S.B S.ρ j hx).eventually
          (eventually_le_nhds (by linarith : S.B.ph x < S.B.ph x + (b - S.B.ph x) / 2))] with t ht _
        exact ht
      · exact Eventually.of_forall fun _ h => absurd h hx
    have hE : ∀ᶠ t in 𝓝[>] (0 : ℝ), S.e1 t < (b - S.B.ph x) / 2 :=
      hS.e1_tendsto_zero.eventually (eventually_lt_nhds hdpos)
    filter_upwards [self_mem_nhdsWithin, hJ, hE] with t ht hJt hEt
    have ht' : 0 < t := ht
    have := boundedPsh_regularised_le S.B S.ρ S.cutoff (lt_of_lt_of_le ht' (S.e1_ge t ht')) x _ hJt
    show S.B.regularised S.ρ t (S.e1 t) S.η x < b
    linarith

/- English proof (translation)
Take `⟨δ, hδ, hmarg⟩` from `S.R.toPotentialCharts.exists_margin`. Establish `hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ` using `Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2`. Use `filter_upwards [self_mem_nhdsWithin, hδ', hS.compare] with t ht htδ hcmp`. Establish `ht' : 0 < t` using `ht`. Establish `hε : 0 < S.e1 t` using `lt_of_lt_of_le ht' (S.e1_ge t ht')`.

Establish `hball : ∀ j, ∀ x ∈ closure (S.R.mid j), closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target` using `fun j x hx => ((closedBall_subset_closedBall htδ.le).trans (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)).trans (hmarg j)`. Conclude with `continuous_of_atlasSmooth (GroundTheory.Heights₂.Heights.Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht' hε hball hcmp).1`.
-/
theorem LogLogRegularisationSetting.continuous_regWeight {A : HermLine ι} (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Continuous (S.regWeight t) := by
  obtain ⟨δ, hδ, hmarg⟩ := S.R.toPotentialCharts.exists_margin
  have hδ' : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ := Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun t ht => ht.2
  filter_upwards [self_mem_nhdsWithin, hδ', hS.compare] with t ht htδ hcmp
  have ht' : 0 < t := ht
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht' (S.e1_ge t ht')
  have hball : ∀ j, ∀ x ∈ closure (S.R.mid j), closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target :=
    fun j x hx => ((closedBall_subset_closedBall htδ.le).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)).trans (hmarg j)
  exact continuous_of_atlasSmooth (GroundTheory.Heights₂.Heights.Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ
    S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht' hε hball hcmp).1

end Settings

section Ratio

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover x`. Establish `hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U` using `⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hx⟩`. Establish `h2` using `(hg j _ hmem).continuousAt.comp ((A.chart j).continuousAt hj)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy`.

Simplify using `[(A.chart j).left_inv hy]`.
-/
theorem holoOn_continuousAt {e : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas e Y} {U : Set Y}
    {g : Y → ℂ} (hg : A.HoloOn U g) {x : Y} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hx⟩
  have h2 := (hg j _ hmem).continuousAt.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `only [Set.ofPred_forall, Set.ofPred_exists]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hP` using `prod_norm_zpow_pos hc A₁.a`. Establish `e1 : A₁.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A₁.a k) * A₁.h z` using `A₁.smul c z hc`. Establish `e2 : A₂.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A₁.a k) * A₂.h z`. Rewrite using `[ha]`. Conclude with `A₂.smul c z hc`.

Rewrite using `[e1, e2, Real.log_mul hP.ne' (A₁.pos z hz).ne', Real.log_mul hP.ne' (A₂.pos z hz).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_ratio_torusSmul (A₁ A₂ : HermLine ι) (ha : A₁.a = A₂.a) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A₁.h (torusSmul c z)) - Real.log (A₂.h (torusSmul c z)) =
      Real.log (A₁.h z) - Real.log (A₂.h z) := by
  have hP := prod_norm_zpow_pos hc A₁.a
  have e1 : A₁.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A₁.a k) * A₁.h z := A₁.smul c z hc
  have e2 : A₂.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A₁.a k) * A₂.h z := by
    rw [ha]; exact A₂.smul c z hc
  rw [e1, e2, Real.log_mul hP.ne' (A₁.pos z hz).ne', Real.log_mul hP.ne' (A₂.pos z hz).ne']
  ring

/- English proof (translation)
The claim follows from `(h₁.continuousOn.log fun z hz => (A₁.pos z hz).ne').sub (h₂.continuousOn.log fun z hz => (A₂.pos z hz).ne')`.
-/
theorem continuousOn_log_ratio (A₁ A₂ : HermLine ι) (h₁ : IsSmoothHerm A₁) (h₂ : IsSmoothHerm A₂) :
    ContinuousOn (fun z => Real.log (A₁.h z) - Real.log (A₂.h z))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  (h₁.continuousOn.log fun z hz => (A₁.pos z hz).ne').sub
    (h₂.continuousOn.log fun z hz => (A₂.pos z hz).ne')

/- English proof (translation)
Use `set L : ((Σ k, ι k) → ℂ) → ℝ := fun z => Real.log (A₁.h z) - Real.log (A₂.h z) with hLdef`. Establish `hL` using `continuousOn_log_ratio A₁ A₂ h₁ h₂`. Establish `key : ∀ x : M.Xc, ∃ b : ℝ, ∃ V ∈ 𝓝 x, ∀ z ∈ mcPts P, M.proj z ∈ V → |L z| ≤ b`. Introduce `x`. Take `⟨U, hUo, hxU, s, hs, hhol⟩` from `M.sections x`.

Establish `hsc : ContinuousAt s x` using `continuousAt_pi.2 fun p => holoOn_continuousAt (hhol p) hxU`. Establish `hsx` using `(hs x hxU).1`. Establish `hLs : ContinuousAt (fun y => L (s y)) x` using `(hL.continuousAt (isOpen_blockNonzero.mem_nhds hsx.1)).comp hsc`. Establish `hev : ∀ᶠ y in 𝓝 x, |L (s y) - L (s x)| < 1`. Use `hLs.eventually (Metric.ball_mem_nhds (L (s x)) one_pos)` as an intermediate fact.

Use `filter_upwards [this] with y hy`. Rewrite `hy` using `[Real.dist_eq]`. Conclude with `hy`. Use `⟨|L (s x)| + 1, {y | y ∈ U ∧ |L (s y) - L (s x)| < 1}, inter_mem (hUo.mem_nhds hxU) hev, fun z hz hzV => ?_⟩` and prove the remaining obligations. Take `⟨hyU, hlt⟩` from `hzV`.

Take `⟨hsm, hsp⟩` from `hs (M.proj z) hyU`. Take `⟨c, hc, hzc⟩` from `(M.fibre _ hsm z hz).1 hsp`. Establish `hLz : L z = L (s (M.proj z))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hLz]`.

Use `abs_sub_abs_le_abs_sub (L (s (M.proj z))) (L (s x))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose b V hV hb using key`. Take `⟨t, -, hcov⟩` from `(isCompact_univ : IsCompact (univ : Set M.Xc)).elim_nhds_subcover V (fun x _ => hV x)`. Use `⟨∑ x ∈ t, |b x|, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨x, hxt, hzx⟩` from `Set.mem_iUnion₂.1 (hcov (mem_univ (M.proj z)))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem CxModel.exists_bound_log_ratio {P : Ideal (MRing ι)} {d : ℕ} (M : CxModel P d) (A₁ A₂ : HermLine ι)
    (ha : A₁.a = A₂.a) (h₁ : IsSmoothHerm A₁) (h₂ : IsSmoothHerm A₂) :
    ∃ C : ℝ, ∀ z ∈ mcPts P, |Real.log (A₁.h z) - Real.log (A₂.h z)| ≤ C := by
  set L : ((Σ k, ι k) → ℂ) → ℝ := fun z => Real.log (A₁.h z) - Real.log (A₂.h z) with hLdef
  have hL := continuousOn_log_ratio A₁ A₂ h₁ h₂
  have key : ∀ x : M.Xc, ∃ b : ℝ, ∃ V ∈ 𝓝 x, ∀ z ∈ mcPts P, M.proj z ∈ V → |L z| ≤ b := by
    intro x
    obtain ⟨U, hUo, hxU, s, hs, hhol⟩ := M.sections x
    have hsc : ContinuousAt s x := continuousAt_pi.2 fun p => holoOn_continuousAt (hhol p) hxU
    have hsx := (hs x hxU).1
    have hLs : ContinuousAt (fun y => L (s y)) x :=
      (hL.continuousAt (isOpen_blockNonzero.mem_nhds hsx.1)).comp hsc
    have hev : ∀ᶠ y in 𝓝 x, |L (s y) - L (s x)| < 1 := by
      have := hLs.eventually (Metric.ball_mem_nhds (L (s x)) one_pos)
      filter_upwards [this] with y hy
      rw [Real.dist_eq] at hy
      exact hy
    refine ⟨|L (s x)| + 1, {y | y ∈ U ∧ |L (s y) - L (s x)| < 1}, inter_mem (hUo.mem_nhds hxU) hev,
      fun z hz hzV => ?_⟩
    obtain ⟨hyU, hlt⟩ := hzV
    obtain ⟨hsm, hsp⟩ := hs (M.proj z) hyU
    obtain ⟨c, hc, hzc⟩ := (M.fibre _ hsm z hz).1 hsp
    have hLz : L z = L (s (M.proj z)) :=
      calc L z = L (torusSmul c (s (M.proj z))) := congrArg L hzc
        _ = L (s (M.proj z)) := log_ratio_torusSmul A₁ A₂ ha c hc hsm.1
    rw [hLz]
    have := abs_sub_abs_le_abs_sub (L (s (M.proj z))) (L (s x))
    linarith
  choose b V hV hb using key
  obtain ⟨t, -, hcov⟩ := (isCompact_univ : IsCompact (univ : Set M.Xc)).elim_nhds_subcover V
    (fun x _ => hV x)
  refine ⟨∑ x ∈ t, |b x|, fun z hz => ?_⟩
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 (hcov (mem_univ (M.proj z)))
  calc |L z| ≤ b x := hb x z hz hzx
    _ ≤ |b x| := le_abs_self _
    _ ≤ ∑ x ∈ t, |b x| := Finset.single_le_sum (fun i _ => abs_nonneg (b i)) hxt

end Ratio

end GroundTheory.Heights₂.Heights.LowerBoundFree
