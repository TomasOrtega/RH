import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)

noncomputable section

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨j, hj⟩` from `A.cover x`. Establish `h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target`. Simplify using `using (hf j).continuousOn`.

Establish `h2` using `(h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp ((A.chart j).continuousAt hj)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy`. Simplify using `[(A.chart j).left_inv hy]`.
-/
theorem continuous_of_atlasSmooth {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    simpa using (hf j).continuousOn
  have h2 := (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
    ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

/- English proof (translation)
Conclude with `((ReciprocityTheory.AnForm.A.regMax_thm ι).1 η hη).2.2.2.1 t`.
-/
theorem regMax_bounds {ι : Type} [Fintype ι] [Nonempty ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2 := by
  classical
  exact ((ReciprocityTheory.AnForm.A.regMax_thm ι).1 η hη).2.2.2.1 t

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

/- English proof (translation)
The claim follows from `isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono (P.closure_mid j))`.
-/
theorem isCompact_image_closure_mid [CompactSpace X] (j : Fin P.N) :
    IsCompact ((P.chart j) '' closure (P.mid j)) :=
  isClosed_closure.isCompact.image_of_continuousOn
    ((P.chart j).continuousOn.mono (P.closure_mid j))

/- English proof (translation)
Establish `h : ∀ j, ∃ δ, 0 < δ ∧ cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target` using `fun j => (P.isCompact_image_closure_mid j).exists_cthickening_subset_open (P.chart j).open_target (image_subset_iff.2 fun x hx => (P.chart j).map_source (P.closure_mid j hx))`. Use `choose δ hδ hsub using h`. Distinguish the cases in `hN : Nonempty (Fin P.N)`. Take `⟨j₀, hj₀⟩` from `Finite.exists_min δ`. Conclude with `⟨δ j₀, hδ j₀, fun j => (cthickening_mono (hj₀ j) _).trans (hsub j)⟩`.

Conclude with `⟨1, one_pos, fun j => (hN ⟨j⟩).elim⟩`.
-/
theorem exists_margin [CompactSpace X] :
    ∃ δ > 0, ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target := by
  have h : ∀ j, ∃ δ, 0 < δ ∧
      cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target :=
    fun j => (P.isCompact_image_closure_mid j).exists_cthickening_subset_open
      (P.chart j).open_target
      (image_subset_iff.2 fun x hx => (P.chart j).map_source (P.closure_mid j hx))
  choose δ hδ hsub using h
  by_cases hN : Nonempty (Fin P.N)
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min δ
    exact ⟨δ j₀, hδ j₀, fun j => (cthickening_mono (hj₀ j) _).trans (hsub j)⟩
  · exact ⟨1, one_pos, fun j => (hN ⟨j⟩).elim⟩

/- English proof (translation)
Establish `h : ∀ j, ∃ Q : ℝ, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), ‖P.q j y‖ ≤ Q` using `fun j => (P.isCompact_image_closure_mid j).cthickening.exists_bound_of_continuousOn ((P.q_smooth j).continuousOn.mono (hδ j))`. Use `choose Q hQ using h`. Use `⟨∑ j, |Q j|, fun j y hy => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bound_q [CompactSpace X] {δ : ℝ}
    (hδ : ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target) :
    ∃ Q : ℝ, ∀ j, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), |P.q j y| ≤ Q := by
  have h : ∀ j, ∃ Q : ℝ, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), ‖P.q j y‖ ≤ Q :=
    fun j => (P.isCompact_image_closure_mid j).cthickening.exists_bound_of_continuousOn
      ((P.q_smooth j).continuousOn.mono (hδ j))
  choose Q hQ using h
  refine ⟨∑ j, |Q j|, fun j y hy => ?_⟩
  calc |P.q j y| = ‖P.q j y‖ := (Real.norm_eq_abs _).symm
    _ ≤ Q j := hQ j y hy
    _ ≤ |Q j| := le_abs_self _
    _ ≤ ∑ j, |Q j| := Finset.single_le_sum (fun i _ => abs_nonneg (Q i)) (Finset.mem_univ j)

end PotentialCharts

/- English proof (translation)
Introduce `X _ _ _ D A B`. Take `⟨ρ⟩` from `ReciprocityTheory.AnForm.A.mollifierInhabit_thm D`. Take `⟨C₀, t₁, ht₁, hcmp⟩` from `h0 X D A B ρ`. Take `⟨η, Cη, hη⟩` from `h2 X D A B.toPotentialCharts`. Take `⟨δ, hδ, hmarg⟩` from `B.toPotentialCharts.exists_margin`.

Take `⟨Q, hQ⟩` from `B.toPotentialCharts.exists_bound_q hmarg`. Take `⟨Cb, hCb⟩` from `B.bdd`. Use `set C₁ : ℝ := max C₀ 1 with hC₁`. Establish `hC₁pos : 0 < C₁` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Use `set ε : ℝ → ℝ := fun t => C₁ / Real.log t⁻¹ + C₁ * t with hε`.

Use `set t₀ : ℝ := min (min t₁ δ) (1 / 2) with ht₀`. Establish `ht₀pos : 0 < t₀` using `lt_min (lt_min ht₁ hδ) (by norm_num)`. Establish `hlog2 : 0 < Real.log 2` using `Real.log_pos one_lt_two`. Establish `hℓ : ∀ t, 0 < t → t < t₀ → Real.log 2 ≤ Real.log t⁻¹`. Introduce `t ht htt`.

Establish `: t ≤ 1 / 2` using `htt.le.trans (min_le_right _ _)`. Apply `Real.log_le_log two_pos` to reduce the goal to its premises. Rewrite using `[le_inv_comm₀ two_pos ht]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hℓpos : ∀ t, 0 < t → t < t₀ → 0 < Real.log t⁻¹` using `fun t ht htt => hlog2.trans_le (hℓ t ht htt)`.

Establish `hεpos : ∀ t, 0 < t → t < t₀ → 0 < ε t` using `fun t ht htt => add_pos (div_pos hC₁pos (hℓpos t ht htt)) (mul_pos hC₁pos ht)`. Establish `hε_le : ∀ t, 0 < t → t < t₀ → ε t ≤ C₁ / Real.log 2 + C₁`. Introduce `t ht htt`. Establish `h1' : t ≤ 1` using `by have := htt.le.trans (min_le_right _ _); linarith`. Establish `e1 : C₁ / Real.log t⁻¹ ≤ C₁ / Real.log 2` using `div_le_div_of_nonneg_left hC₁pos.le hlog2 (hℓ t ht htt)`.

Establish `e2 : C₁ * t ≤ C₁` using `by nlinarith`. Simplify using `only [hε]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hε_le' : ∀ t, 0 < t → t < t₀ → ε t ≤ 2 * C₁ / Real.log t⁻¹`. Introduce `t ht htt`.

Establish `hl` using `hℓpos t ht htt`. Establish `htl : t * Real.log t⁻¹ ≤ 1`. Use `Real.log_le_sub_one_of_pos (inv_pos.2 ht)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `e1 : C₁ * t ≤ C₁ / Real.log t⁻¹`.

Rewrite using `[le_div_iff₀ hl]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left htl hC₁pos.le]`. Establish `e2 : 2 * C₁ / Real.log t⁻¹ = C₁ / Real.log t⁻¹ + C₁ / Real.log t⁻¹` using `by ring`. Simplify using `only [hε]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK : ∀ j, ∀ x ∈ closure (B.mid j), B.chart j x ∈ cthickening δ ((B.chart j) '' closure (B.mid j))` using `fun j x hx => self_subset_cthickening _ (mem_image_of_mem _ hx)`. Establish `hball' : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ cthickening δ ((B.chart j) '' closure (B.mid j))`. Introduce `t ht htt j x hx`. Establish `: t ≤ δ` using `htt.le.trans ((min_le_left _ _).trans (min_le_right _ _))`. Conclude with `(closedBall_subset_closedBall this).trans (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)`.

Establish `hball : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target` using `fun t ht htt j x hx => (hball' t ht htt j x hx).trans (hmarg j)`. Establish `hmol` using `fun j => h3 D ρ (B.chart j).target (B.u j) (B.chart j).open_target (B.u_psh j)`. Establish `hsrc : ∀ j, ∀ x ∈ B.mid j, x ∈ (B.chart j).source` using `fun j x hx => B.mid_subset_source j hx`. Establish `hu : ∀ j, ∀ x ∈ B.mid j, B.u j (B.chart j x) = B.q j (B.chart j x) + B.ph x`. Introduce `j x hx`.

Simplify using `only [BoundedPshData.u, PotentialCharts.chartFun, (B.chart j).left_inv (hsrc j x hx)]`. Establish `hlow : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ B.mid j, B.ph x ≤ B.phReg ρ t j x`. Introduce `t ht htt j x hx`. Establish `hz : B.chart j x ∈ shrink (B.chart j).target t` using `hball t ht htt j x (subset_closure hx)`. Use `(((hmol j).1 t ht).2.2.2 _ hz).1` as an intermediate fact.

Rewrite `this` using `[hu j x hx]`. Simplify using `only [BoundedPshData.phReg, BoundedPshData.smoothed]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hupj : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ B.mid j, B.phReg ρ t j x ≤ 2 * Q + Cb`. Introduce `t ht htt j x hx`.

Establish `hz : B.chart j x ∈ shrink (B.chart j).target t` using `hball t ht htt j x (subset_closure hx)`. Establish `e1` using `(((hmol j).1 t ht).2.2.2 _ hz).2`. Establish `e2 : polyMax (B.u j) (B.chart j x) t ≤ Q + Cb`. Unfold `ReciprocityTheory.AnForm.A.polyMax`. Apply `csSup_le ((nonempty_closedBall.2 ht.le).image _)` to reduce the goal to its premises.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `f1` using `hQ j y (hball' t ht htt j x (subset_closure hx) hy)`. Establish `f2` using `hCb ((B.chart j).symm y)`. Establish `f3` using `le_abs_self (B.q j y)`. Establish `f4` using `le_abs_self (B.ph ((B.chart j).symm y))`.

Simplify using `only [BoundedPshData.u, PotentialCharts.chartFun]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3` using `hQ j _ (hK j x (subset_closure hx))`. Establish `e4` using `neg_abs_le (B.q j (B.chart j x))`. Simplify using `only [BoundedPshData.phReg, BoundedPshData.smoothed]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hconvj : ∀ j, ∀ x ∈ B.mid j, Tendsto (fun t => B.phReg ρ t j x) (𝓝[>] 0) (𝓝 (B.ph x))`. Introduce `j x hx`. Use `((hmol j).2 _ ((B.chart j).map_source (hsrc j x hx))).sub_const (B.q j (B.chart j x))` as an intermediate fact. Rewrite `this` using `[hu j x hx, add_sub_cancel_left]`.

Conclude with `this`. Establish `hφlow : ∀ t, 0 < t → t < t₀ → ∀ x, B.ph x ≤ B.regularised ρ t (ε t) η x`. Introduce `t ht htt x`. Take `⟨j₀, hj₀⟩` from `B.cover x`. Establish `hx₀ : x ∈ B.mid j₀` using `B.inner_subset_mid j₀ hj₀`.

Establish `hb` using `regMax_bounds (ι := {j // x ∈ B.mid j}) (hεpos t ht htt) (fun j => B.phReg ρ t j x + 4 * ε t * η j x)`. Establish `hle : B.phReg ρ t j₀ x + 4 * ε t * η j₀ x ≤ tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x)` using `Finset.le_sup' (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x) (Finset.mem_univ ⟨j₀, hx₀⟩)`. Rewrite `hle` using `[hη.eq_zero j₀ x hj₀]`. Establish `e1` using `hlow t ht htt j₀ x hx₀`. Establish `e2` using `(hεpos t ht htt).le`.

Simplify using `only [BoundedPshData.regularised, PotentialCharts.glue]`. Combine the linear relations using `[hb.1]`. Establish `hφup : ∀ t, 0 < t → t < t₀ → ∀ x (M : ℝ), (∀ j, x ∈ B.mid j → B.phReg ρ t j x ≤ M) → B.regularised ρ t (ε t) η x ≤ M + ε t`. Introduce `t ht htt x M hM`. Establish `hb` using `regMax_bounds (ι := {j // x ∈ B.mid j}) (hεpos t ht htt) (fun j => B.phReg ρ t j x + 4 * ε t * η j x)`.

Establish `hle : tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x) ≤ M` using `Finset.sup'_le _ _ fun j _ => by`. Establish `e1` using `(hη.bounds j.1 x j.2).2`. Establish `e2` using `hM j.1 j.2`. Establish `e3 : 4 * ε t * η j x ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by linarith [hεpos t ht htt]) e1`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [BoundedPshData.regularised, PotentialCharts.glue]`. Combine the linear relations using `[hb.2]`. Establish `hε0 : Tendsto ε (𝓝[>] 0) (𝓝 0)`. Establish `hlog : Tendsto (fun t : ℝ => Real.log t⁻¹) (𝓝[>] 0) atTop` using `Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero`. Establish `ha : Tendsto (fun t : ℝ => C₁ / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0)` using `tendsto_const_nhds.div_atTop hlog`.

Establish `hb : Tendsto (fun t : ℝ => C₁ * t) (𝓝[>] 0) (𝓝 0)`. Establish `: Tendsto (fun t : ℝ => C₁ * t) (𝓝 0) (𝓝 (C₁ * 0))` using `tendsto_const_nhds.mul tendsto_id`. Rewrite `this` using `[mul_zero]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `ha.add hb` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `this`. Establish `hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < t₀` using `Ioo_mem_nhdsGT ht₀pos`. Establish `hpt : ∀ x, Tendsto (fun t => B.regularised ρ t (ε t) η x) (𝓝[>] 0) (𝓝 (B.ph x))`. Introduce `x`.

Rewrite using `[tendsto_order]`. Use `⟨fun a ha => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hI] with t ht`. Conclude with `ha.trans_le (hφlow t ht.1 ht.2 x)`. Establish `hdpos : 0 < (b - B.ph x) / 2` using `by linarith`.

Establish `hJ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, x ∈ B.mid j → B.phReg ρ t j x ≤ B.ph x + (b - B.ph x) / 2`. Rewrite using `[eventually_all]`. Introduce `j`. Distinguish the cases in `hx : x ∈ B.mid j`. Use `filter_upwards [(hconvj j x hx).eventually (eventually_le_nhds (by linarith : B.ph x < B.ph x + (b - B.ph x) / 2))] with t ht _`.

Conclude with `ht`. Conclude with `Eventually.of_forall fun _ h => absurd h hx`. Establish `hE : ∀ᶠ t in 𝓝[>] (0 : ℝ), ε t < (b - B.ph x) / 2` using `hε0.eventually (eventually_lt_nhds hdpos)`. Use `filter_upwards [hI, hJ, hE] with t ht hJt hEt`. Use `hφup t ht.1 ht.2 x _ hJt` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcmp' : ∀ t, 0 < t → t < t₀ → ∀ j k, ∀ x ∈ B.mid j ∩ B.mid k, |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε t`. Introduce `t ht htt j k x hx`. Establish `hl` using `hℓpos t ht htt`. Establish `e0` using `hcmp t ht (htt.trans_le ((min_le_left _ _).trans (min_le_left _ _))) j k x hx`.

Establish `e1 : C₀ / Real.log t⁻¹ ≤ C₁ / Real.log t⁻¹` using `div_le_div_of_nonneg_right (le_max_left _ _) hl.le`. Establish `e2 : C₀ * t ≤ C₁ * t` using `mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le`. Simplify using `only [hε]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hglue` using `fun t (ht : 0 < t) (htt : t < t₀) => h1 X D A B ρ η Cη t (ε t) hη ht (hεpos t ht htt) (hball t ht htt) (hcmp' t ht htt)`.

Use `set Cup : ℝ := 2 * Q + Cb + (C₁ / Real.log 2 + C₁) with hCup`. Use `set C : ℝ := max (8 * max Cη 0 * C₁) Cup with hC`. Establish `hφC : ∀ t, 0 < t → t < t₀ → ∀ x, B.regularised ρ t (ε t) η x ≤ C`. Introduce `t ht htt x`. Establish `e1` using `hφup t ht htt x (2 * Q + Cb) (fun j hj => hupj t ht htt j x hj)`.

Establish `e2` using `hε_le t ht htt`. Establish `e3 : Cup ≤ C` using `le_max_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbd : ∀ t, 0 < t → t < t₀ → ∀ x, |B.regularised ρ t (ε t) η x - B.ph x| ≤ C + Cb`. Introduce `t ht htt x`.

Establish `e1` using `hφlow t ht htt x`. Establish `e2` using `hφC t ht htt x`. Establish `e3` using `hCb x`. Establish `e4` using `neg_abs_le (B.ph x)`. Rewrite using `[abs_of_nonneg (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨C, t₀, fun t => B.regularised ρ t (ε t) η, ht₀pos, ?_, ?_, fun x _ => hpt x⟩` and prove the remaining obligations. Introduce `t ht htt`. Use `⟨(hglue t ht htt).1, fun x => ⟨hφlow t ht htt x, hφC t ht htt x⟩, fun k x hx w => ?_⟩` and prove the remaining obligations. Establish `hl` using `hℓpos t ht htt`.

Establish `hgk` using `(hglue t ht htt).2 k x hx w`. Establish `hw : 0 ≤ ‖w‖ ^ 2` using `by positivity`. Establish `key : 4 * Cη * ε t ≤ C / Real.log t⁻¹`. Establish `e0` using `(hεpos t ht htt).le`. Establish `e1 : 4 * Cη * ε t ≤ 4 * max Cη 0 * ε t`.

Use `le_max_left Cη 0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : 4 * max Cη 0 * ε t ≤ 4 * max Cη 0 * (2 * C₁ / Real.log t⁻¹)` using `mul_le_mul_of_nonneg_left (hε_le' t ht htt) (by positivity)`. Establish `e3 : 4 * max Cη 0 * (2 * C₁ / Real.log t⁻¹) = 8 * max Cη 0 * C₁ / Real.log t⁻¹`. Expand and normalize the polynomial expressions, which then agree.

Establish `e4 : 8 * max Cη 0 * C₁ / Real.log t⁻¹ ≤ C / Real.log t⁻¹` using `div_le_div_of_nonneg_right (le_max_left _ _) hl.le`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(mul_le_mul_of_nonneg_right (neg_le_neg key) hw).trans hgk`. Introduce `k`. Establish `hsub : B.chartMid k ⊆ (B.chart k).target` using `inter_subset_left`.

Establish `hopen : IsOpen (B.chartMid k)` using `(B.chart k).continuousOn_symm.isOpen_inter_preimage (B.chart k).open_target (B.isOpen_mid k)`. Establish `hmeas : MeasurableSet (B.chartMid k)` using `hopen.measurableSet`. Establish `hfin : volume (B.chartMid k) ≠ ⊤` using `((isBounded_ball (x := (0 : Fin D → ℂ)) (r := 1)).subset (hsub.trans (B.target_subset k))).measure_lt_top.ne`. Establish `: IsFiniteMeasure (volume.restrict (B.chartMid k))` using `isFiniteMeasure_restrict.2 hfin`. Establish `hcont : ∀ t, 0 < t → t < t₀ → ContinuousOn (fun y => B.regularised ρ t (ε t) η ((B.chart k).symm y)) (B.chartMid k)` using `fun t ht htt => (continuous_of_atlasSmooth (hglue t ht htt).1).comp_continuousOn ((B.chart k).continuousOn_symm.mono hsub)`.

Establish `hspos : ∀ n : ℕ, 0 < t₀ / ((n + 2 : ℕ) : ℝ)` using `fun n => div_pos ht₀pos (by positivity)`. Establish `hslt : ∀ n : ℕ, t₀ / ((n + 2 : ℕ) : ℝ) < t₀` using `fun n => by`. Rewrite using `[div_lt_iff₀ (by positivity)]`. Establish `: (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ)` using `by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hs0 : Tendsto (fun n : ℕ => t₀ / ((n + 2 : ℕ) : ℝ)) atTop (𝓝[>] 0)` using `tendsto_nhdsWithin_iff.2 ⟨(tendsto_const_div_atTop_nhds_zero_nat t₀).comp (tendsto_add_atTop_nat 2), Eventually.of_forall hspos⟩`. Establish `hphm : AEStronglyMeasurable (fun y => B.ph ((B.chart k).symm y)) (volume.restrict (B.chartMid k))` using `aestronglyMeasurable_of_tendsto_ae (u := atTop) (fun n => (hcont _ (hspos n) (hslt n)).aestronglyMeasurable hmeas) (ae_of_all _ fun y => (hpt _).comp hs0)`. Establish `hdiff : ∀ t, 0 < t → t < t₀ → AEStronglyMeasurable (fun y => B.regularised ρ t (ε t) η ((B.chart k).symm y) - B.ph ((B.chart k).symm y)) (volume.restrict (B.chartMid k))` using `fun t ht htt => ((hcont t ht htt).aestronglyMeasurable hmeas).sub hphm`. Use `⟨fun t ht htt => ⟨hdiff t ht htt, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := C + Cb) hfin.lt_top (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hbd t ht htt _)`.

Establish `hdc` using `tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (B.chartMid k)) (F := fun t y => |B.regularised ρ t (ε t) η ((B.chart k).symm y) - B.ph ((B.chart k).symm y)|) (f := fun _ => 0) (fun _ => C + Cb) (hI.mono fun t ht => (hdiff t ht.1 ht.2).norm) (hI.mono fun t …`. Rewrite using `[Real.norm_eq_abs, abs_abs]`. Conclude with `hbd t ht.1 ht.2 _)`. Use the proof step `(integrable_const _)`. Use the proof step `(ae_of_all _ fun y => by`.

Use `((hpt ((B.chart k).symm y)).sub_const (B.ph ((B.chart k).symm y))).abs` as an intermediate fact. Rewrite `this` using `[sub_self, abs_zero]`. Conclude with `this)`. Rewrite `hdc` using `[integral_zero]`. Conclude with `hdc`.
-/
theorem BoundedRegularisation.proof (h0 : BoundedChartComparison.Statement)
    (h1 : BoundedGlue.Statement) (h2 : CutoffsExist.Statement)
    (h3 : ReciprocityTheory.AnForm.A.MollifyStatement) : BoundedRegularisation.Statement := by
  classical
  intro X _ _ _ D A B
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨C₀, t₁, ht₁, hcmp⟩ := h0 X D A B ρ
  obtain ⟨η, Cη, hη⟩ := h2 X D A B.toPotentialCharts
  obtain ⟨δ, hδ, hmarg⟩ := B.toPotentialCharts.exists_margin
  obtain ⟨Q, hQ⟩ := B.toPotentialCharts.exists_bound_q hmarg
  obtain ⟨Cb, hCb⟩ := B.bdd
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε : ℝ → ℝ := fun t => C₁ / Real.log t⁻¹ + C₁ * t with hε
  set t₀ : ℝ := min (min t₁ δ) (1 / 2) with ht₀
  have ht₀pos : 0 < t₀ := lt_min (lt_min ht₁ hδ) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two

  have hℓ : ∀ t, 0 < t → t < t₀ → Real.log 2 ≤ Real.log t⁻¹ := by
    intro t ht htt
    have : t ≤ 1 / 2 := htt.le.trans (min_le_right _ _)
    apply Real.log_le_log two_pos
    rw [le_inv_comm₀ two_pos ht]
    linarith
  have hℓpos : ∀ t, 0 < t → t < t₀ → 0 < Real.log t⁻¹ :=
    fun t ht htt => hlog2.trans_le (hℓ t ht htt)
  have hεpos : ∀ t, 0 < t → t < t₀ → 0 < ε t := fun t ht htt =>
    add_pos (div_pos hC₁pos (hℓpos t ht htt)) (mul_pos hC₁pos ht)
  have hε_le : ∀ t, 0 < t → t < t₀ → ε t ≤ C₁ / Real.log 2 + C₁ := by
    intro t ht htt
    have h1' : t ≤ 1 := by have := htt.le.trans (min_le_right _ _); linarith
    have e1 : C₁ / Real.log t⁻¹ ≤ C₁ / Real.log 2 :=
      div_le_div_of_nonneg_left hC₁pos.le hlog2 (hℓ t ht htt)
    have e2 : C₁ * t ≤ C₁ := by nlinarith
    simp only [hε]
    linarith
  have hε_le' : ∀ t, 0 < t → t < t₀ → ε t ≤ 2 * C₁ / Real.log t⁻¹ := by
    intro t ht htt
    have hl := hℓpos t ht htt
    have htl : t * Real.log t⁻¹ ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
      calc t * Real.log t⁻¹ ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left this ht.le
        _ = 1 - t := by rw [mul_sub, mul_inv_cancel₀ ht.ne', mul_one]
        _ ≤ 1 := by linarith
    have e1 : C₁ * t ≤ C₁ / Real.log t⁻¹ := by
      rw [le_div_iff₀ hl]
      nlinarith [mul_le_mul_of_nonneg_left htl hC₁pos.le]
    have e2 : 2 * C₁ / Real.log t⁻¹ = C₁ / Real.log t⁻¹ + C₁ / Real.log t⁻¹ := by ring
    simp only [hε]
    linarith

  have hK : ∀ j, ∀ x ∈ closure (B.mid j),
      B.chart j x ∈ cthickening δ ((B.chart j) '' closure (B.mid j)) :=
    fun j x hx => self_subset_cthickening _ (mem_image_of_mem _ hx)
  have hball' : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ closure (B.mid j),
      closedBall (B.chart j x) t ⊆ cthickening δ ((B.chart j) '' closure (B.mid j)) := by
    intro t ht htt j x hx
    have : t ≤ δ := htt.le.trans ((min_le_left _ _).trans (min_le_right _ _))
    exact (closedBall_subset_closedBall this).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) δ)
  have hball : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ closure (B.mid j),
      closedBall (B.chart j x) t ⊆ (B.chart j).target :=
    fun t ht htt j x hx => (hball' t ht htt j x hx).trans (hmarg j)

  have hmol := fun j => h3 D ρ (B.chart j).target (B.u j) (B.chart j).open_target (B.u_psh j)
  have hsrc : ∀ j, ∀ x ∈ B.mid j, x ∈ (B.chart j).source :=
    fun j x hx => B.mid_subset_source j hx
  have hu : ∀ j, ∀ x ∈ B.mid j, B.u j (B.chart j x) = B.q j (B.chart j x) + B.ph x := by
    intro j x hx
    simp only [BoundedPshData.u, PotentialCharts.chartFun, (B.chart j).left_inv (hsrc j x hx)]
  have hlow : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ B.mid j, B.ph x ≤ B.phReg ρ t j x := by
    intro t ht htt j x hx
    have hz : B.chart j x ∈ shrink (B.chart j).target t :=
      hball t ht htt j x (subset_closure hx)
    have := (((hmol j).1 t ht).2.2.2 _ hz).1
    rw [hu j x hx] at this
    simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
    linarith
  have hupj : ∀ t, 0 < t → t < t₀ → ∀ j, ∀ x ∈ B.mid j, B.phReg ρ t j x ≤ 2 * Q + Cb := by
    intro t ht htt j x hx
    have hz : B.chart j x ∈ shrink (B.chart j).target t :=
      hball t ht htt j x (subset_closure hx)
    have e1 := (((hmol j).1 t ht).2.2.2 _ hz).2
    have e2 : polyMax (B.u j) (B.chart j x) t ≤ Q + Cb := by
      unfold ReciprocityTheory.AnForm.A.polyMax
      apply csSup_le ((nonempty_closedBall.2 ht.le).image _)
      rintro _ ⟨y, hy, rfl⟩
      have f1 := hQ j y (hball' t ht htt j x (subset_closure hx) hy)
      have f2 := hCb ((B.chart j).symm y)
      have f3 := le_abs_self (B.q j y)
      have f4 := le_abs_self (B.ph ((B.chart j).symm y))
      simp only [BoundedPshData.u, PotentialCharts.chartFun]
      linarith
    have e3 := hQ j _ (hK j x (subset_closure hx))
    have e4 := neg_abs_le (B.q j (B.chart j x))
    simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
    linarith
  have hconvj : ∀ j, ∀ x ∈ B.mid j,
      Tendsto (fun t => B.phReg ρ t j x) (𝓝[>] 0) (𝓝 (B.ph x)) := by
    intro j x hx
    have := ((hmol j).2 _ ((B.chart j).map_source (hsrc j x hx))).sub_const
      (B.q j (B.chart j x))
    rw [hu j x hx, add_sub_cancel_left] at this
    exact this

  have hφlow : ∀ t, 0 < t → t < t₀ → ∀ x, B.ph x ≤ B.regularised ρ t (ε t) η x := by
    intro t ht htt x
    obtain ⟨j₀, hj₀⟩ := B.cover x
    have hx₀ : x ∈ B.mid j₀ := B.inner_subset_mid j₀ hj₀
    have hb := regMax_bounds (ι := {j // x ∈ B.mid j}) (hεpos t ht htt)
      (fun j => B.phReg ρ t j x + 4 * ε t * η j x)
    have hle : B.phReg ρ t j₀ x + 4 * ε t * η j₀ x ≤
        tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x) :=
      Finset.le_sup' (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x)
        (Finset.mem_univ ⟨j₀, hx₀⟩)
    rw [hη.eq_zero j₀ x hj₀] at hle
    have e1 := hlow t ht htt j₀ x hx₀
    have e2 := (hεpos t ht htt).le
    simp only [BoundedPshData.regularised, PotentialCharts.glue]
    linarith [hb.1]
  have hφup : ∀ t, 0 < t → t < t₀ → ∀ x (M : ℝ), (∀ j, x ∈ B.mid j → B.phReg ρ t j x ≤ M) →
      B.regularised ρ t (ε t) η x ≤ M + ε t := by
    intro t ht htt x M hM
    have hb := regMax_bounds (ι := {j // x ∈ B.mid j}) (hεpos t ht htt)
      (fun j => B.phReg ρ t j x + 4 * ε t * η j x)
    have hle : tmax (fun j : {j // x ∈ B.mid j} => B.phReg ρ t j x + 4 * ε t * η j x) ≤ M :=
      Finset.sup'_le _ _ fun j _ => by
        have e1 := (hη.bounds j.1 x j.2).2
        have e2 := hM j.1 j.2
        have e3 : 4 * ε t * η j x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith [hεpos t ht htt]) e1
        linarith
    simp only [BoundedPshData.regularised, PotentialCharts.glue]
    linarith [hb.2]

  have hε0 : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have hlog : Tendsto (fun t : ℝ => Real.log t⁻¹) (𝓝[>] 0) atTop :=
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have ha : Tendsto (fun t : ℝ => C₁ / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hb : Tendsto (fun t : ℝ => C₁ * t) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C₁ * t) (𝓝 0) (𝓝 (C₁ * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ha.add hb
    rw [add_zero] at this
    exact this
  have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < t₀ := Ioo_mem_nhdsGT ht₀pos

  have hpt : ∀ x, Tendsto (fun t => B.regularised ρ t (ε t) η x) (𝓝[>] 0) (𝓝 (B.ph x)) := by
    intro x
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [hI] with t ht
      exact ha.trans_le (hφlow t ht.1 ht.2 x)
    · have hdpos : 0 < (b - B.ph x) / 2 := by linarith
      have hJ : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, x ∈ B.mid j →
          B.phReg ρ t j x ≤ B.ph x + (b - B.ph x) / 2 := by
        rw [eventually_all]
        intro j
        by_cases hx : x ∈ B.mid j
        · filter_upwards [(hconvj j x hx).eventually
            (eventually_le_nhds (by linarith : B.ph x < B.ph x + (b - B.ph x) / 2))] with t ht _
          exact ht
        · exact Eventually.of_forall fun _ h => absurd h hx
      have hE : ∀ᶠ t in 𝓝[>] (0 : ℝ), ε t < (b - B.ph x) / 2 :=
        hε0.eventually (eventually_lt_nhds hdpos)
      filter_upwards [hI, hJ, hE] with t ht hJt hEt
      have := hφup t ht.1 ht.2 x _ hJt
      linarith

  have hcmp' : ∀ t, 0 < t → t < t₀ → ∀ j k, ∀ x ∈ B.mid j ∩ B.mid k,
      |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε t := by
    intro t ht htt j k x hx
    have hl := hℓpos t ht htt
    have e0 := hcmp t ht (htt.trans_le ((min_le_left _ _).trans (min_le_left _ _))) j k x hx
    have e1 : C₀ / Real.log t⁻¹ ≤ C₁ / Real.log t⁻¹ :=
      div_le_div_of_nonneg_right (le_max_left _ _) hl.le
    have e2 : C₀ * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le
    simp only [hε]
    linarith
  have hglue := fun t (ht : 0 < t) (htt : t < t₀) =>
    h1 X D A B ρ η Cη t (ε t) hη ht (hεpos t ht htt) (hball t ht htt) (hcmp' t ht htt)
  set Cup : ℝ := 2 * Q + Cb + (C₁ / Real.log 2 + C₁) with hCup
  set C : ℝ := max (8 * max Cη 0 * C₁) Cup with hC
  have hφC : ∀ t, 0 < t → t < t₀ → ∀ x, B.regularised ρ t (ε t) η x ≤ C := by
    intro t ht htt x
    have e1 := hφup t ht htt x (2 * Q + Cb) (fun j hj => hupj t ht htt j x hj)
    have e2 := hε_le t ht htt
    have e3 : Cup ≤ C := le_max_right _ _
    linarith
  have hbd : ∀ t, 0 < t → t < t₀ → ∀ x, |B.regularised ρ t (ε t) η x - B.ph x| ≤ C + Cb := by
    intro t ht htt x
    have e1 := hφlow t ht htt x
    have e2 := hφC t ht htt x
    have e3 := hCb x
    have e4 := neg_abs_le (B.ph x)
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine ⟨C, t₀, fun t => B.regularised ρ t (ε t) η, ht₀pos, ?_, ?_, fun x _ => hpt x⟩
  · intro t ht htt
    refine ⟨(hglue t ht htt).1, fun x => ⟨hφlow t ht htt x, hφC t ht htt x⟩, fun k x hx w => ?_⟩
    have hl := hℓpos t ht htt
    have hgk := (hglue t ht htt).2 k x hx w
    have hw : 0 ≤ ‖w‖ ^ 2 := by positivity
    have key : 4 * Cη * ε t ≤ C / Real.log t⁻¹ := by
      have e0 := (hεpos t ht htt).le
      have e1 : 4 * Cη * ε t ≤ 4 * max Cη 0 * ε t := by
        have := le_max_left Cη 0
        nlinarith
      have e2 : 4 * max Cη 0 * ε t ≤ 4 * max Cη 0 * (2 * C₁ / Real.log t⁻¹) :=
        mul_le_mul_of_nonneg_left (hε_le' t ht htt) (by positivity)
      have e3 : 4 * max Cη 0 * (2 * C₁ / Real.log t⁻¹) = 8 * max Cη 0 * C₁ / Real.log t⁻¹ := by
        ring
      have e4 : 8 * max Cη 0 * C₁ / Real.log t⁻¹ ≤ C / Real.log t⁻¹ :=
        div_le_div_of_nonneg_right (le_max_left _ _) hl.le
      linarith
    exact (mul_le_mul_of_nonneg_right (neg_le_neg key) hw).trans hgk
  · intro k
    have hsub : B.chartMid k ⊆ (B.chart k).target := inter_subset_left
    have hopen : IsOpen (B.chartMid k) :=
      (B.chart k).continuousOn_symm.isOpen_inter_preimage (B.chart k).open_target (B.isOpen_mid k)
    have hmeas : MeasurableSet (B.chartMid k) := hopen.measurableSet
    have hfin : volume (B.chartMid k) ≠ ⊤ :=
      ((isBounded_ball (x := (0 : Fin D → ℂ)) (r := 1)).subset
        (hsub.trans (B.target_subset k))).measure_lt_top.ne
    have : IsFiniteMeasure (volume.restrict (B.chartMid k)) := isFiniteMeasure_restrict.2 hfin
    have hcont : ∀ t, 0 < t → t < t₀ →
        ContinuousOn (fun y => B.regularised ρ t (ε t) η ((B.chart k).symm y)) (B.chartMid k) :=
      fun t ht htt => (continuous_of_atlasSmooth (hglue t ht htt).1).comp_continuousOn
        ((B.chart k).continuousOn_symm.mono hsub)

    have hspos : ∀ n : ℕ, 0 < t₀ / ((n + 2 : ℕ) : ℝ) := fun n => div_pos ht₀pos (by positivity)
    have hslt : ∀ n : ℕ, t₀ / ((n + 2 : ℕ) : ℝ) < t₀ := fun n => by
      rw [div_lt_iff₀ (by positivity)]
      have : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      nlinarith
    have hs0 : Tendsto (fun n : ℕ => t₀ / ((n + 2 : ℕ) : ℝ)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨(tendsto_const_div_atTop_nhds_zero_nat t₀).comp
        (tendsto_add_atTop_nat 2), Eventually.of_forall hspos⟩
    have hphm : AEStronglyMeasurable (fun y => B.ph ((B.chart k).symm y))
        (volume.restrict (B.chartMid k)) :=
      aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (fun n => (hcont _ (hspos n) (hslt n)).aestronglyMeasurable hmeas)
        (ae_of_all _ fun y => (hpt _).comp hs0)
    have hdiff : ∀ t, 0 < t → t < t₀ → AEStronglyMeasurable
        (fun y => B.regularised ρ t (ε t) η ((B.chart k).symm y) - B.ph ((B.chart k).symm y))
        (volume.restrict (B.chartMid k)) :=
      fun t ht htt => ((hcont t ht htt).aestronglyMeasurable hmeas).sub hphm
    refine ⟨fun t ht htt => ⟨hdiff t ht htt, ?_⟩, ?_⟩
    · exact MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := C + Cb) hfin.lt_top
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hbd t ht htt _)
    · have hdc := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (B.chartMid k))
        (F := fun t y => |B.regularised ρ t (ε t) η ((B.chart k).symm y) -
          B.ph ((B.chart k).symm y)|)
        (f := fun _ => 0) (fun _ => C + Cb)
        (hI.mono fun t ht => (hdiff t ht.1 ht.2).norm)
        (hI.mono fun t ht => ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_abs]; exact hbd t ht.1 ht.2 _)
        (integrable_const _)
        (ae_of_all _ fun y => by
          have := ((hpt ((B.chart k).symm y)).sub_const (B.ph ((B.chart k).symm y))).abs
          rw [sub_self, abs_zero] at this
          exact this)
      rw [integral_zero] at hdc
      exact hdc

end

end GroundTheory.Heights₂.Heights.Regular
