import Mathlib

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals

variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]

def pd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Q : X × M → V) (q : X × M) : X →L[ℝ] V :=
  fderiv ℝ (fun x => Q (x, q.2)) q.1

omit [FiniteDimensional ℝ X] in
/- English proof (translation)
Introduce `q hq`. Establish `hQa : ContDiffAt ℝ ∞ Q q` using `hQ.contDiffAt ((hU.prod hW).mem_nhds hq)`. Use `ContDiffAt.contDiffWithinAt ?_` and prove the remaining obligations. Use `ContDiffAt.fderiv (f := fun (r : X × M) (x : X) => Q (x, r.2)) (g := fun r => r.1) ?_ contDiffAt_fst ENat.coe_top_add_one.le` and prove the remaining obligations. Establish `e : Function.uncurry (fun (r : X × M) (x : X) => Q (x, r.2)) = Q ∘ fun z : (X × M) × X => (z.2, z.1.2)` using `rfl`.

Rewrite using `[e]`. Conclude with `ContDiffAt.comp _ hQa (contDiffAt_snd.prodMk (contDiffAt_snd.comp _ contDiffAt_fst))`.
-/
theorem contDiffOn_pd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Q : X × M → V} {U : Set X} {W : Set M}
    (hU : IsOpen U) (hW : IsOpen W) (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) : ContDiffOn ℝ ∞ (pd Q) (U ×ˢ W) := by
  intro q hq
  have hQa : ContDiffAt ℝ ∞ Q q := hQ.contDiffAt ((hU.prod hW).mem_nhds hq)
  refine ContDiffAt.contDiffWithinAt ?_
  refine ContDiffAt.fderiv (f := fun (r : X × M) (x : X) => Q (x, r.2)) (g := fun r => r.1) ?_ contDiffAt_fst
    ENat.coe_top_add_one.le
  have e : Function.uncurry (fun (r : X × M) (x : X) => Q (x, r.2)) = Q ∘ fun z : (X × M) × X => (z.2, z.1.2) := rfl
  rw [e]
  exact ContDiffAt.comp _ hQa (contDiffAt_snd.prodMk (contDiffAt_snd.comp _ contDiffAt_fst))

variable {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {U : Set X} {W : Set M} {p : T → M}

/- English proof (translation)
Take `⟨K, hK, hKe⟩` from `hs x₀ hx₀`. Establish `hUW` using `hU.prod hW`. Take `⟨δ, hδ, hδK⟩` from `Metric.eventually_nhds_iff_ball.1 hKe`. Take `⟨ε₀, hε₀, hε₀U⟩` from `Metric.isOpen_iff.1 hU x₀ hx₀`. Use `set ε := min (δ / 2) (ε₀ / 2) with hεdef`.

Establish `hε : 0 < ε` using `lt_min (half_pos hδ) (half_pos hε₀)`. Establish `hcb : closedBall x₀ ε ⊆ U` using `fun x hx => hε₀U (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₀))))`. Establish `hcbδ : closedBall x₀ ε ⊆ ball x₀ δ` using `fun x hx => mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)))`. Establish `hQc : ContinuousOn Q (U ×ˢ W)` using `hQ.continuousOn`. Establish `hPc : ContinuousOn (pd Q) (U ×ˢ W)` using `(contDiffOn_pd hU hW hQ).continuousOn`.

Establish `hcpt : IsCompact (closedBall x₀ ε ×ˢ (p '' K))` using `(isCompact_closedBall x₀ ε).prod (hK.image hp)`. Establish `hsub : closedBall x₀ ε ×ˢ (p '' K) ⊆ U ×ˢ W` using `prod_mono hcb (by rintro _ ⟨y, -, rfl⟩; exact hpW y)`. Take `⟨C, hC⟩` from `hcpt.exists_bound_of_continuousOn (hPc.mono hsub)`. Establish `hzero : ∀ x ∈ ball x₀ δ, ∀ y ∉ K, pd Q (x, p y) = 0`. Introduce `x hx y hy`.

Establish `h0 : (fun x' => Q (x', p y)) =ᶠ[𝓝 x] fun _ => 0` using `by filter_upwards [isOpen_ball.mem_nhds hx] with x' hx' using hδK x' hx' y hy`. Use `show fderiv ℝ (fun x' => Q (x', p y)) x = 0`. Rewrite using `[h0.fderiv_eq]`. Conclude with `fderiv_const_apply _`. Establish `hdiff : ∀ x ∈ U, ∀ y, HasFDerivAt (fun x' => Q (x', p y)) (pd Q (x, p y)) x`.

Introduce `x hx y`. Establish `h1 : ContDiffAt ℝ ∞ Q (x, p y)` using `hQ.contDiffAt (hUW.mem_nhds ⟨hx, hpW y⟩)`. Establish `h2 : DifferentiableAt ℝ (fun x' => Q (x', p y)) x` using `(h1.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))`. Conclude with `h2.hasFDerivAt`. Establish `hcont : ∀ x ∈ U, Continuous fun y => Q (x, p y)` using `fun x hx => hQc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩`.

Establish `hcont' : ∀ x ∈ U, Continuous fun y => pd Q (x, p y)` using `fun x hx => hPc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (F := fun x y => Q (x, p y)) (F' := fun x y => pd Q (x, p y)) (s := ball x₀ ε) (bound := K.indicator fun _ => C) (ball_mem_nhds x₀ hε) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds hx₀] with x hx using (hcont x hx).aestronglyMeasurable`. Conclude with `(hcont x₀ hx₀).integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun y hy => hδK x₀ (mem_ball_self hδ) y hy)`. Conclude with `(hcont' x₀ hx₀).aestronglyMeasurable`.

Use `ae_of_all _ fun y x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ K`. Rewrite using `[indicator_of_mem hy]`. Conclude with `hC _ ⟨ball_subset_closedBall hx, mem_image_of_mem p hy⟩`. Rewrite using `[hzero x (hcbδ (ball_subset_closedBall hx)) y hy, indicator_of_notMem hy, norm_zero]`.

Conclude with `(integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet`. Conclude with `ae_of_all _ fun y x hx => hdiff x (hcb (ball_subset_closedBall hx)) y`.
-/
theorem hasFDerivAt_step (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0)
    {x₀ : X} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ y, Q (x, p y) ∂μ) (∫ y, pd Q (x₀, p y) ∂μ) x₀ := by
  obtain ⟨K, hK, hKe⟩ := hs x₀ hx₀
  have hUW := hU.prod hW
  obtain ⟨δ, hδ, hδK⟩ := Metric.eventually_nhds_iff_ball.1 hKe
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set ε := min (δ / 2) (ε₀ / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos hε₀)
  have hcb : closedBall x₀ ε ⊆ U := fun x hx =>
    hε₀U (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₀))))
  have hcbδ : closedBall x₀ ε ⊆ ball x₀ δ := fun x hx =>
    mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)))
  have hQc : ContinuousOn Q (U ×ˢ W) := hQ.continuousOn
  have hPc : ContinuousOn (pd Q) (U ×ˢ W) := (contDiffOn_pd hU hW hQ).continuousOn
  have hcpt : IsCompact (closedBall x₀ ε ×ˢ (p '' K)) := (isCompact_closedBall x₀ ε).prod (hK.image hp)
  have hsub : closedBall x₀ ε ×ˢ (p '' K) ⊆ U ×ˢ W := prod_mono hcb (by rintro _ ⟨y, -, rfl⟩; exact hpW y)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hPc.mono hsub)
  have hzero : ∀ x ∈ ball x₀ δ, ∀ y ∉ K, pd Q (x, p y) = 0 := by
    intro x hx y hy
    have h0 : (fun x' => Q (x', p y)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with x' hx' using hδK x' hx' y hy
    show fderiv ℝ (fun x' => Q (x', p y)) x = 0
    rw [h0.fderiv_eq]
    exact fderiv_const_apply _
  have hdiff : ∀ x ∈ U, ∀ y, HasFDerivAt (fun x' => Q (x', p y)) (pd Q (x, p y)) x := by
    intro x hx y
    have h1 : ContDiffAt ℝ ∞ Q (x, p y) := hQ.contDiffAt (hUW.mem_nhds ⟨hx, hpW y⟩)
    have h2 : DifferentiableAt ℝ (fun x' => Q (x', p y)) x :=
      (h1.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))
    exact h2.hasFDerivAt
  have hcont : ∀ x ∈ U, Continuous fun y => Q (x, p y) := fun x hx =>
    hQc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩
  have hcont' : ∀ x ∈ U, Continuous fun y => pd Q (x, p y) := fun x hx =>
    hPc.comp_continuous (continuous_const.prodMk hp) fun y => ⟨hx, hpW y⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (F := fun x y => Q (x, p y))
    (F' := fun x y => pd Q (x, p y)) (s := ball x₀ ε) (bound := K.indicator fun _ => C)
    (ball_mem_nhds x₀ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hU.mem_nhds hx₀] with x hx using (hcont x hx).aestronglyMeasurable
  · exact (hcont x₀ hx₀).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun y hy => hδK x₀ (mem_ball_self hδ) y hy)
  · exact (hcont' x₀ hx₀).aestronglyMeasurable
  · refine ae_of_all _ fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      exact hC _ ⟨ball_subset_closedBall hx, mem_image_of_mem p hy⟩
    · rw [hzero x (hcbδ (ball_subset_closedBall hx)) y hy, indicator_of_notMem hy, norm_zero]
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  · exact ae_of_all _ fun y x hx => hdiff x (hcb (ball_subset_closedBall hx)) y

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V _ _ _ Q hQ hs`. Rewrite using `[Nat.cast_zero, contDiffOn_zero]`. Conclude with `fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).continuousAt.continuousWithinAt`.

Consider the case `succ n ih`. Introduce `V _ _ _ Q hQ hs`. Rewrite using `[Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]`. Use `⟨fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩` and prove the remaining obligations. Establish `hs' : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, pd Q (x', p y) = 0`.

Introduce `x hx`. Take `⟨K, hK, hKe⟩` from `hs x hx`. Use `⟨K, hK, ?_⟩` and prove the remaining obligations. Use `filter_upwards [eventually_eventually_nhds.2 hKe] with x' hx' y hy`. Establish `h0 : (fun x'' => Q (x'', p y)) =ᶠ[𝓝 x'] fun _ => 0` using `hx'.mono fun x'' h => h y hy`.

Use `show fderiv ℝ (fun x'' => Q (x'', p y)) x' = 0`. Rewrite using `[h0.fderiv_eq]`. Conclude with `fderiv_const_apply _`. Conclude with `(ih (X →L[ℝ] V) (pd Q) (contDiffOn_pd hU hW hQ) hs').congr fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).fderiv`.
-/
theorem contDiffOn_integral_nat (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : X × M → V),
      ContDiffOn ℝ ∞ Q (U ×ˢ W) → (∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, Q (x, p y) ∂μ) U := by
  induction n with
  | zero =>
    intro V _ _ _ Q hQ hs
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ Q hQ hs
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hs' : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, pd Q (x', p y) = 0 := by
      intro x hx
      obtain ⟨K, hK, hKe⟩ := hs x hx
      refine ⟨K, hK, ?_⟩
      filter_upwards [eventually_eventually_nhds.2 hKe] with x' hx' y hy
      have h0 : (fun x'' => Q (x'', p y)) =ᶠ[𝓝 x'] fun _ => 0 := hx'.mono fun x'' h => h y hy
      show fderiv ℝ (fun x'' => Q (x'', p y)) x' = 0
      rw [h0.fderiv_eq]
      exact fderiv_const_apply _
    exact (ih (X →L[ℝ] V) (pd Q) (contDiffOn_pd hU hW hQ) hs').congr fun x hx =>
      (hasFDerivAt_step (μ := μ) hU hW hp hpW hQ hs hx).fderiv

/- English proof (translation)
The claim follows from `contDiffOn_infty.2 fun n => contDiffOn_integral_nat hU hW hp hpW n V Q hQ hs`.
-/
theorem contDiffOn_integral (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ y, Q (x, p y) ∂μ) U :=
  contDiffOn_infty.2 fun n => contDiffOn_integral_nat hU hW hp hpW n V Q hQ hs

end PositivityTheory.Rg.BcB.CG.SmoothIntegrals

end
