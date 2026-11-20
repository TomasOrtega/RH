import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaGraphPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal
open Set Metric

noncomputable section

/- English proof (translation)
Introduce `k m U F hU hF r hr`. Establish `hcont : ContinuousOn (fderiv ℝ F) U` using `hF.continuousOn_fderiv_of_isOpen hU le_rfl`. Establish `hdiff : ∀ x ∈ U, DifferentiableAt ℝ F x` using `fun x hx => (hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)`. Establish `hball : ∀ x : U, ∃ ε > 0, ball (x : EuclideanSpace ℝ (Fin k)) ε ⊆ U ∧ ∀ y ∈ ball (x : EuclideanSpace ℝ (Fin k)) ε, ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ r (fderiv ℝ F x)`. Introduce `x`.

Establish `hpos : (0 : ℝ) < r (fderiv ℝ F x)` using `NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hr _))`. Establish `hca : ContinuousAt (fderiv ℝ F) x` using `hcont.continuousAt (hU.mem_nhds x.2)`. Take `⟨δ, δpos, hδ⟩` from `Metric.continuousAt_iff.1 hca _ hpos`. Take `⟨η, ηpos, hη⟩` from `Metric.isOpen_iff.1 hU x x.2`. Use `⟨min δ η, lt_min δpos ηpos, (ball_subset_ball (min_le_right _ _)).trans hη, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Use `hδ (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))` as an intermediate fact. Rewrite `this` using `[dist_eq_norm]`. Conclude with `this.le`. Use `choose ε εpos hεU hεD using hball`.

Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun x : U => ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) (fun _ => isOpen_ball)`. Establish `hcover : (⋃ x : U, ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) = U`. Apply `Subset.antisymm` to reduce the goal to its premises. Conclude with `iUnion_subset fun x => hεU x`. Introduce `x hx`.

Conclude with `mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (εpos _)⟩`. Break down `U.eq_empty_or_nonempty with hUe | hUne` into its components or cases. Use `⟨fun _ => ∅, fun _ => 0, fun _ _ _ => disjoint_empty _, fun _ => MeasurableSet.empty, fun _ => empty_subset _, by simp [hUe], fun _ => fun x hx => absurd hx (notMem_empty x), fun _ x hx => absurd hx (notMem_empty x)⟩` and prove the remaining obligations. Establish `hTne : T.Nonempty`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_nonempty_iff_eq_empty]`. Take `⟨x, hx⟩` from `hUne`. Establish `: x ∈ ⋃ i ∈ T, ball ((i : U) : EuclideanSpace ℝ (Fin k)) (ε i)` using `by rw [hTU, hcover]; exact hx`. Simplify using `[h] at this`. Take `⟨c, hc⟩` from `hTc.exists_eq_range hTne`.

Use `set B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => ball ((c n : U) : EuclideanSpace ℝ (Fin k)) (ε (c n)) with hB`. Establish `hBU : ⋃ n, B n = U`. Rewrite using `[← hcover, ← hTU, hc, biUnion_range]`. Use `⟨disjointed B, fun n => fderiv ℝ F (c n), disjoint_disjointed B, MeasurableSet.disjointed (fun n => measurableSet_ball), fun n => (disjointed_subset B n).trans (hεU (c n)), by rw [iUnion_disjointed, hBU], ?_, ?_⟩` and prove the remaining obligations. Introduce `n x hx y hy`.

Establish `hx'` using `disjointed_subset B n hx`. Establish `hy'` using `disjointed_subset B n hy`. Conclude with `(convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le' (fun z hz => hdiff z (hεU (c n) hz)) (fun z hz => hεD (c n) z hz) hy' hx'`. Introduce `n x hx`. Rewrite using `[← NNReal.coe_le_coe, coe_nnnorm]`.

Conclude with `hεD (c n) x (disjointed_subset B n hx)`.
-/
theorem AreaGraphPartition.proof : AreaGraphPartition.Statement := by
  intro k m U F hU hF r hr

  have hcont : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)

  have hball : ∀ x : U, ∃ ε > 0, ball (x : EuclideanSpace ℝ (Fin k)) ε ⊆ U ∧
      ∀ y ∈ ball (x : EuclideanSpace ℝ (Fin k)) ε, ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ r (fderiv ℝ F x) := by
    intro x
    have hpos : (0 : ℝ) < r (fderiv ℝ F x) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hr _))
    have hca : ContinuousAt (fderiv ℝ F) x := hcont.continuousAt (hU.mem_nhds x.2)
    obtain ⟨δ, δpos, hδ⟩ := Metric.continuousAt_iff.1 hca _ hpos
    obtain ⟨η, ηpos, hη⟩ := Metric.isOpen_iff.1 hU x x.2
    refine ⟨min δ η, lt_min δpos ηpos, (ball_subset_ball (min_le_right _ _)).trans hη, ?_⟩
    intro y hy
    have := hδ (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
    rw [dist_eq_norm] at this
    exact this.le
  choose ε εpos hεU hεD using hball

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) (fun _ => isOpen_ball)
  have hcover : (⋃ x : U, ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => hεU x
    · intro x hx
      exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (εpos _)⟩
  rcases U.eq_empty_or_nonempty with hUe | hUne
  ·
    refine ⟨fun _ => ∅, fun _ => 0, fun _ _ _ => disjoint_empty _, fun _ => MeasurableSet.empty,
      fun _ => empty_subset _, by simp [hUe], fun _ => fun x hx => absurd hx (notMem_empty x),
      fun _ x hx => absurd hx (notMem_empty x)⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hUne
    have : x ∈ ⋃ i ∈ T, ball ((i : U) : EuclideanSpace ℝ (Fin k)) (ε i) := by rw [hTU, hcover]; exact hx
    simp [h] at this
  obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => ball ((c n : U) : EuclideanSpace ℝ (Fin k)) (ε (c n)) with hB
  have hBU : ⋃ n, B n = U := by
    rw [← hcover, ← hTU, hc, biUnion_range]
  refine ⟨disjointed B, fun n => fderiv ℝ F (c n), disjoint_disjointed B,
    MeasurableSet.disjointed (fun n => measurableSet_ball), fun n => (disjointed_subset B n).trans
    (hεU (c n)), by rw [iUnion_disjointed, hBU], ?_, ?_⟩
  · intro n x hx y hy
    have hx' := disjointed_subset B n hx
    have hy' := disjointed_subset B n hy
    exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hdiff z (hεU (c n) hz)) (fun z hz => hεD (c n) z hz) hy' hx'
  · intro n x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hεD (c n) x (disjointed_subset B n hx)

end

end GroundTheory.Heights₂.Heights
