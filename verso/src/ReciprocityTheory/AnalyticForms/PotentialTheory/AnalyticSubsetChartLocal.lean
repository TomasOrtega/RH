import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

/- English proof (translation)
Take `⟨x, ⟨-, hxs⟩, rfl⟩` from `hz`. Take `⟨W₀, hW₀, hxW₀, r, f, hf, hSW⟩` from `hS x`. Establish `hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀)` using `(A.chart j).isOpen_inter_preimage_symm hW₀`. Establish `hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀`. Use `⟨(A.chart j).map_source hxs, ?_⟩` and prove the remaining obligations.

Use `show (A.chart j).symm ((A.chart j) x) ∈ W₀`. Rewrite using `[(A.chart j).left_inv hxs]`. Conclude with `hxW₀`. Take `⟨ε, hε0, hε⟩` from `Metric.isOpen_iff.mp hopen _ hmem`. Establish `hex : ∃ i, ∃ w ∈ Metric.ball ((A.chart j) x) ε, f i ((A.chart j).symm w) ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hsub : (A.chart j).symm '' Metric.ball ((A.chart j) x) ε ⊆ S`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hw'` using `hε hw`.

Establish `hin : (A.chart j).symm w ∈ S ∩ W₀`. Rewrite using `[hSW]`. Conclude with `⟨hw'.2, fun i => hcon i w hw⟩`. Conclude with `hin.1`. Establish `hop : IsOpen ((A.chart j).symm '' Metric.ball ((A.chart j) x) ε)` using `(A.chart j).symm.isOpen_image_of_subset_source Metric.isOpen_ball (fun w hw => (hε hw).1)`.

Establish `hint' : (A.chart j).symm ((A.chart j) x) ∈ interior S` using `interior_maximal hsub hop ⟨_, Metric.mem_ball_self hε0, rfl⟩`. Rewrite `hint'` using `[hint]`. Conclude with `hint'`. Take `⟨i, w₀, hw₀, hfw₀⟩` from `hex`. Use `⟨Metric.ball ((A.chart j) x) ε, Metric.isOpen_ball, Metric.mem_ball_self hε0, (convex_ball _ _).isPreconnected, f i ∘ (A.chart j).symm, ?_, ⟨w₀, hw₀, hfw₀⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(hf i j).mono hε`. Introduce and unpack `w ⟨⟨y, ⟨hyS, hys⟩, rfl⟩, hw⟩`. Establish `hw'` using `hε hw`. Establish `hin : (A.chart j).symm ((A.chart j) y) ∈ S ∩ W₀` using `⟨by rw [(A.chart j).left_inv hys]; exact hyS, hw'.2⟩`. Rewrite `hin` using `[hSW]`.

Conclude with `hin.2 i`.
-/
theorem analyticSubset_chart_local {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {S : Set X} (hS : A.IsAnalyticSubset S) (hint : interior S = ∅) (j : Fin A.n)
    {z : Fin e → ℂ} (hz : z ∈ (A.chart j) '' (S ∩ (A.chart j).source)) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ (A.chart j) '' (S ∩ (A.chart j).source) ∩ W, f w = 0 := by
  obtain ⟨x, ⟨-, hxs⟩, rfl⟩ := hz
  obtain ⟨W₀, hW₀, hxW₀, r, f, hf, hSW⟩ := hS x
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀) :=
    (A.chart j).isOpen_inter_preimage_symm hW₀
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀ := by
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ W₀
    rw [(A.chart j).left_inv hxs]
    exact hxW₀
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen _ hmem

  have hex : ∃ i, ∃ w ∈ Metric.ball ((A.chart j) x) ε, f i ((A.chart j).symm w) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (A.chart j).symm '' Metric.ball ((A.chart j) x) ε ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' := hε hw
      have hin : (A.chart j).symm w ∈ S ∩ W₀ := by
        rw [hSW]
        exact ⟨hw'.2, fun i => hcon i w hw⟩
      exact hin.1
    have hop : IsOpen ((A.chart j).symm '' Metric.ball ((A.chart j) x) ε) :=
      (A.chart j).symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun w hw => (hε hw).1)
    have hint' : (A.chart j).symm ((A.chart j) x) ∈ interior S :=
      interior_maximal hsub hop ⟨_, Metric.mem_ball_self hε0, rfl⟩
    rw [hint] at hint'
    exact hint'
  obtain ⟨i, w₀, hw₀, hfw₀⟩ := hex
  refine ⟨Metric.ball ((A.chart j) x) ε, Metric.isOpen_ball, Metric.mem_ball_self hε0,
    (convex_ball _ _).isPreconnected, f i ∘ (A.chart j).symm, ?_, ⟨w₀, hw₀, hfw₀⟩, ?_⟩
  · exact (hf i j).mono hε
  · rintro w ⟨⟨y, ⟨hyS, hys⟩, rfl⟩, hw⟩
    have hw' := hε hw
    have hin : (A.chart j).symm ((A.chart j) y) ∈ S ∩ W₀ :=
      ⟨by rw [(A.chart j).left_inv hys]; exact hyS, hw'.2⟩
    rw [hSW] at hin
    exact hin.2 i

/- English proof (translation)
Introduce `e X _ A S hS hint j`. Conclude with `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _ (fun z hz => analyticSubset_chart_local A hS hint j hz)`.
-/
theorem analyticNull : AnalyticNullStatement := by
  intro e X _ A S hS hint j
  exact ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _
    (fun z hz => analyticSubset_chart_local A hS hint j hz)

/- English proof (translation)
Use `first`. Consider the case `unfold integralWith`. Consider the case `simp only [integralWith]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Establish `hT : MeasurableSet (A.chart j).target` using `(A.chart j).open_target.measurableSet`.

Establish `hnull : volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0` using `analyticNull A S hS hint j`. Establish `hsub : {y | ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y = P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)} ∩ (A.chart j).target ⊆ (A.chart j) '' (S ∩ (A.chart j).source)`. Introduce `y hy`. Establish `hne : ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y = P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)` using `hy.1`. Establish `hyt : y ∈ (A.chart j).target` using `hy.2`.

Use `⟨(A.chart j).symm y, ⟨?_, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnS`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hg _ hnS]`. Establish `hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target), P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y = P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y`.

Rewrite using `[MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply' hT]`. Conclude with `MeasureTheory.measure_mono_null hsub hnull`. Conclude with `MeasureTheory.integral_congr_ae hae`.
-/
theorem integralWith_congr_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) {S : Set X} (hS : A.IsAnalyticSubset S)
    (hint : interior S = ∅) {g g' : X → ℝ} (hg : ∀ x ∉ S, g x = g' x) :
    integralWith A P Φ g = integralWith A P Φ g' := by
  first
  | unfold integralWith
  | simp only [integralWith]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hnull : volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0 :=
    analyticNull A S hS hint j
  have hsub : {y | ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)} ∩
      (A.chart j).target ⊆ (A.chart j) '' (S ∩ (A.chart j).source) := by
    intro y hy
    have hne : ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y) := hy.1
    have hyt : y ∈ (A.chart j).target := hy.2
    refine ⟨(A.chart j).symm y, ⟨?_, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
    by_contra hnS
    apply hne
    rw [hg _ hnS]
  have hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y := by
    rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply' hT]
    exact MeasureTheory.measure_mono_null hsub hnull
  exact MeasureTheory.integral_congr_ae hae

/- English proof (translation)
Unfold `MIntCongrNullStatement`. Introduce `e X _ A Φ S hS hint g g' hg`. Unfold `mInt`. Use `split_ifs with h`. Conclude with `integralWith_congr_null A h.some Φ hS hint hg`.

Both sides reduce to the same expression.
-/
theorem mIntCongrNull : MIntCongrNullStatement := by
  unfold MIntCongrNullStatement
  intro e X _ A Φ S hS hint g g' hg
  unfold mInt
  split_ifs with h
  · exact integralWith_congr_null A h.some Φ hS hint hg
  · rfl

end

end ReciprocityTheory.AnForm.M
