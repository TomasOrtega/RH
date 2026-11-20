import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsChartBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncPsh
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)

noncomputable section

/- English proof (translation)
Unfold `RegChartData.trunc limsupExt`. Use `split_ifs with hA`. Use `ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)` as an intermediate fact. Establish `hbdd : IsBoundedUnder (· ≤ ·) (𝓝[(R.chart j).target \ coordDiv (R.S j)] y) (fun y => max (R.u j y) (-K))`. Use `isBoundedUnder_of_eventually_le (a := B) ?_` and prove the remaining obligations.

Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy), self_mem_nhdsWithin] with y' hy'V hy'`. Establish `h` using `hb y' hy'V`. Simplify using `only [RegChartData.trunc, limsupExt, if_neg hy'.2] at h`. Conclude with `h`. Use `le_limsup_of_le hbdd (fun b hb' => ?_)` and prove the remaining obligations.

Take `⟨y', hy'⟩` from `hb'.exists`. Conclude with `(le_max_right _ _).trans hy'`. Conclude with `le_max_right (R.u j y) (-K)`.
-/
theorem trunc_ge_of_bdd {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (K B : ℝ) (j : Fin R.N) {V : Set (Fin D → ℂ)} (hVo : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) (hb : ∀ y ∈ V, R.trunc K j y ≤ B) {y : Fin D → ℂ} (hy : y ∈ V) :
    -K ≤ R.trunc K j y := by
  unfold RegChartData.trunc limsupExt
  split_ifs with hA
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)
    have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[(R.chart j).target \ coordDiv (R.S j)] y)
        (fun y => max (R.u j y) (-K)) := by
      refine isBoundedUnder_of_eventually_le (a := B) ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy), self_mem_nhdsWithin]
        with y' hy'V hy'
      have h := hb y' hy'V
      simp only [RegChartData.trunc, limsupExt, if_neg hy'.2] at h
      exact h
    refine le_limsup_of_le hbdd (fun b hb' => ?_)
    obtain ⟨y', hy'⟩ := hb'.exists
    exact (le_max_right _ _).trans hy'
  · exact le_max_right (R.u j y) (-K)

/- English proof (translation)
Take `⟨-, hi⟩` from `ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz`. Rewrite using `[ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]`. Use `_ ≤ _ := by`.

Use `integral_mono ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _) (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z) fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : ρ.scaled t y = 0`. Simplify using `[hy]`. Use `mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)` and prove the remaining obligations. Establish `hmem` using `ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z`.

Rewrite using `[indicator_of_mem hmem]`. Conclude with `hc _ hmem`.
-/
theorem le_molli_of_ge {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, c ≤ φ y) : c ≤ molli ρ t φ z := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc c = ∫ y, ρ.scaled t y * c := by
        rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]
    _ ≤ _ := by
      refine integral_mono ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _)
        (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z) fun y => ?_
      by_cases hy : ρ.scaled t y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
      have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
      rw [indicator_of_mem hmem]
      exact hc _ hmem

/- English proof (translation)
Introduce `X _ _ _ D A R ρ`. Take `⟨δ, B, hδ, hV⟩` from `h X D A R`. Use `choose V hVo hVt hVball hVpsh using hV`. Establish `hcpt : ∀ j, IsCompact (R.chart j '' closure (R.mid j))` using `fun j => isClosed_closure.isCompact.image_of_continuousOn ((R.chart j).continuousOn.mono (R.closure_mid j))`. Establish `himg : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target`.

Introduce and unpack `j _ ⟨x, hx, rfl⟩`. Conclude with `(R.chart j).map_source (R.closure_mid j hx)`. Use `choose r hr hrt using fun j => (hcpt j).exists_cthickening_subset_open (R.chart j).open_target (himg j)`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ j, ε ≤ r j := by`. Break down `isEmpty_or_nonempty (Fin R.N) with hN | hN` into its components or cases.

Conclude with `⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩`. Take `⟨j₀, -, hj₀⟩` from `Finset.univ.exists_min_image r Finset.univ_nonempty`. Conclude with `⟨r j₀, hr j₀, fun j => hj₀ j (Finset.mem_univ j)⟩`. Use `choose Cq hCq using fun j => (hcpt j).exists_bound_of_continuousOn (((R.q_smooth j).continuousOn).mono (himg j))`. Use `⟨max B 0 + ∑ j, |Cq j|, min δ ε, lt_min hδ hε, fun t ht ht₀ => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `j x hx`. Conclude with `(closedBall_subset_cthickening (mem_image_of_mem _ hx) t).trans ((cthickening_mono ((ht₀.trans_le (min_le_right _ _)).le.trans (hεr j)) _).trans (hrt j))`. Introduce `K hK j x hx`. Establish `hxs : x ∈ (R.chart j).source` using `R.closure_mid j (subset_closure hx)`. Take `⟨hpsh, hbd⟩` from `hVpsh j K`.

Establish `htδ : t ≤ δ` using `(ht₀.trans_le (min_le_left _ _)).le`. Establish `hball : closedBall (R.chart j x) t ⊆ V j` using `(closedBall_subset_closedBall htδ).trans (hVball j x hx)`. Establish `hq : |R.q j (R.chart j x)| ≤ ∑ j, |Cq j|`. Establish `h1` using `hCq j (R.chart j x) (mem_image_of_mem _ (subset_closure hx))`. Rewrite `h1` using `[Real.norm_eq_abs]`.

Conclude with `h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cq j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))`. Establish `hlow : -K ≤ molli ρ t (R.trunc K j) (R.chart j x)` using `le_molli_of_ge ρ (hVo j) hpsh ht hball fun y hy => trunc_ge_of_bdd R K _ j (hVo j) (hVt j) hbd (hball hy)`. Establish `hup : molli ρ t (R.trunc K j) (R.chart j x) ≤ max B 0`. Establish `h1` using `ReciprocityTheory.AnForm.A.molli_le_polyMax ρ (hVo j) hpsh ht (z := R.chart j x) hball`. Use `h1.trans (ReciprocityTheory.AnForm.A.polyMax_le' ht.le fun y hy => ?_)` and prove the remaining obligations.

Conclude with `(hbd y (hball hy)).trans (max_le_max le_rfl (by linarith))`. Establish `hphReg : R.phReg ρ K t j x = molli ρ t (R.trunc K j) (R.chart j x) - R.q j (R.chart j x)` using `rfl`. Use `⟨?_, ?_, fun hY => ?_⟩` and prove the remaining obligations. Rewrite using `[hphReg]`. Combine the linear relations using `[neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]`.

Rewrite using `[hphReg]`. Combine the linear relations using `[neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]`. Establish `hA : R.chart j x ∉ coordDiv (R.S j)` using `(R.mem_Yo j x hxs).1 hY`. Establish `htr : R.trunc K j (R.chart j x) = max (R.u j (R.chart j x)) (-K)`. Simplify using `only [RegChartData.trunc, limsupExt, if_neg hA]`.

Establish `hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x`. Simplify using `only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hxs]`. Establish `hle` using `ReciprocityTheory.AnForm.A.le_molli ρ (hVo j) hpsh ht (z := R.chart j x) hball`. Rewrite using `[hphReg]`. Combine the linear relations using `[le_max_left (R.u j (R.chart j x)) (-K)]`.
-/
theorem ChartMollifiedBounds.proof (h : TruncPsh.Statement) : ChartMollifiedBounds.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B, hδ, hV⟩ := h X D A R
  choose V hVo hVt hVball hVpsh using hV

  have hcpt : ∀ j, IsCompact (R.chart j '' closure (R.mid j)) := fun j =>
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have himg : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro j _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  choose r hr hrt using fun j => (hcpt j).exists_cthickening_subset_open (R.chart j).open_target (himg j)

  obtain ⟨ε, hε, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ j, ε ≤ r j := by
    rcases isEmpty_or_nonempty (Fin R.N) with hN | hN
    · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
      exact ⟨r j₀, hr j₀, fun j => hj₀ j (Finset.mem_univ j)⟩

  choose Cq hCq using fun j => (hcpt j).exists_bound_of_continuousOn
    (((R.q_smooth j).continuousOn).mono (himg j))
  refine ⟨max B 0 + ∑ j, |Cq j|, min δ ε, lt_min hδ hε, fun t ht ht₀ => ⟨?_, ?_⟩⟩
  · intro j x hx
    exact (closedBall_subset_cthickening (mem_image_of_mem _ hx) t).trans
      ((cthickening_mono ((ht₀.trans_le (min_le_right _ _)).le.trans (hεr j)) _).trans (hrt j))
  intro K hK j x hx
  have hxs : x ∈ (R.chart j).source := R.closure_mid j (subset_closure hx)
  obtain ⟨hpsh, hbd⟩ := hVpsh j K
  have htδ : t ≤ δ := (ht₀.trans_le (min_le_left _ _)).le
  have hball : closedBall (R.chart j x) t ⊆ V j :=
    (closedBall_subset_closedBall htδ).trans (hVball j x hx)
  have hq : |R.q j (R.chart j x)| ≤ ∑ j, |Cq j| := by
    have h1 := hCq j (R.chart j x) (mem_image_of_mem _ (subset_closure hx))
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Cq j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))

  have hlow : -K ≤ molli ρ t (R.trunc K j) (R.chart j x) :=
    le_molli_of_ge ρ (hVo j) hpsh ht hball fun y hy =>
      trunc_ge_of_bdd R K _ j (hVo j) (hVt j) hbd (hball hy)
  have hup : molli ρ t (R.trunc K j) (R.chart j x) ≤ max B 0 := by
    have h1 := ReciprocityTheory.AnForm.A.molli_le_polyMax ρ (hVo j) hpsh ht (z := R.chart j x) hball
    refine h1.trans (ReciprocityTheory.AnForm.A.polyMax_le' ht.le fun y hy => ?_)
    exact (hbd y (hball hy)).trans (max_le_max le_rfl (by linarith))
  have hphReg : R.phReg ρ K t j x = molli ρ t (R.trunc K j) (R.chart j x) - R.q j (R.chart j x) := rfl
  refine ⟨?_, ?_, fun hY => ?_⟩
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  ·
    have hA : R.chart j x ∉ coordDiv (R.S j) := (R.mem_Yo j x hxs).1 hY
    have htr : R.trunc K j (R.chart j x) = max (R.u j (R.chart j x)) (-K) := by
      simp only [RegChartData.trunc, limsupExt, if_neg hA]
    have hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x := by
      simp only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hxs]
    have hle := ReciprocityTheory.AnForm.A.le_molli ρ (hVo j) hpsh ht (z := R.chart j x) hball
    rw [hphReg]
    linarith [le_max_left (R.u j (R.chart j x)) (-K)]

end

end GroundTheory.Heights₂.Heights.Regular
