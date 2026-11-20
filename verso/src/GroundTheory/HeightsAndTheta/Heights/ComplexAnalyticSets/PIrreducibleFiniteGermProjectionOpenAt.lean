import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleFiniteGermProjectionOpenAt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPointsOffDiscriminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

/- English proof (translation)
Introduce `σ _ X x d A hX hirr hiso hinj V hV`. Take `⟨δ, hδa, hδne, hδpts⟩` from `hpts σ X x d A hX hirr hiso hinj`. Take `⟨N, k, f, hNo, hxN, hf, hXN⟩` from `hX`. Take `⟨r, hr, hrV⟩` from `Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))`. Use `set r' := r / 2 with hr'`.

Establish `hr'0 : 0 < r'` using `by positivity`. Establish `hcb : closedBall x r' ⊆ V ∩ N` using `(closedBall_subset_ball (by linarith)).trans hrV`. Use `set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK`. Establish `hKc : IsCompact K`. Use `(isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left` and prove the remaining obligations.

Use `isClosed_closedBall.inter (isClosed_iInter fun i => ?_)` and prove the remaining obligations. Conclude with `((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton`. Establish `hKV : A '' K ⊆ A '' (X ∩ V)`. Use `image_mono fun z hz => ?_` and prove the remaining obligations. Establish `hzN : z ∈ N` using `(hcb hz.1).2`.

Establish `hzX : z ∈ X ∩ N`. Rewrite using `[hXN]`. Conclude with `⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩`. Conclude with `⟨hzX.1, (hcb hz.1).1⟩`. Establish `hball : ∀ z ∈ X ∩ ball x r', z ∈ K`.

Introduce `z hz`. Establish `hzcb : z ∈ closedBall x r'` using `ball_subset_closedBall hz.2`. Establish `hzN : z ∈ X ∩ N` using `⟨hz.1, (hcb hzcb).2⟩`. Rewrite `hzN` using `[hXN]`. Conclude with `⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩`.

Take `⟨ε₁, hε₁, hε₁a⟩` from `hδa.exists_ball_analyticOnNhd`. Take `⟨ε₂, hε₂, hε₂p⟩` from `Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))`. Use `set ε := min ε₁ ε₂`. Establish `hε : 0 < ε` using `lt_min hε₁ hε₂`. Establish `hDa : AnalyticOnNhd ℂ δ (ball (A x) ε)` using `hε₁a.mono (ball_subset_ball (min_le_left _ _))`.

Establish `hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K`. Introduce and unpack `y ⟨hy, hδy⟩`. Establish `hy2 : dist y (A x) < ε₂` using `lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)`. Take `⟨x', hx', rfl⟩` from `hε₂p hy2 hδy`. Conclude with `⟨x', hball x' hx', rfl⟩`.

Establish `hD : ball (A x) ε ⊆ A '' K`. Introduce `y hy`. Use `(hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)` and prove the remaining obligations. Introduce `hev`. Establish `hev' : δ =ᶠ[𝓝 y] 0` using `by filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD`.

Assume the negation of the conclusion as `hz0`. Conclude with `hz ⟨hzD, hz0⟩`. Establish `hzero` using `hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'`. Apply `hδne` to reduce the goal to its premises. Use `filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz`.

Conclude with `Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)`.
-/
theorem IrreducibleFiniteGermProjectionOpenAt.proof
    (hpts : IrreducibleGermPointsOffDiscriminant.Statement) :
    IrreducibleFiniteGermProjectionOpenAt.Statement := by
  intro σ _ X x d A hX hirr hiso hinj V hV
  obtain ⟨δ, hδa, hδne, hδpts⟩ := hpts σ X x d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))
  set r' := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hcb : closedBall x r' ⊆ V ∩ N := (closedBall_subset_ball (by linarith)).trans hrV

  set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKV : A '' K ⊆ A '' (X ∩ V) := by
    refine image_mono fun z hz => ?_
    have hzN : z ∈ N := (hcb hz.1).2
    have hzX : z ∈ X ∩ N := by
      rw [hXN]
      exact ⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩
    exact ⟨hzX.1, (hcb hz.1).1⟩
  have hball : ∀ z ∈ X ∩ ball x r', z ∈ K := by
    intro z hz
    have hzcb : z ∈ closedBall x r' := ball_subset_closedBall hz.2
    have hzN : z ∈ X ∩ N := ⟨hz.1, (hcb hzcb).2⟩
    rw [hXN] at hzN
    exact ⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩

  obtain ⟨ε₁, hε₁, hε₁a⟩ := hδa.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hε₂p⟩ := Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ (ball (A x) ε) := hε₁a.mono (ball_subset_ball (min_le_left _ _))
  have hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K := by
    rintro y ⟨hy, hδy⟩
    have hy2 : dist y (A x) < ε₂ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)
    obtain ⟨x', hx', rfl⟩ := hε₂p hy2 hδy
    exact ⟨x', hball x' hx', rfl⟩
  have hD : ball (A x) ε ⊆ A '' K := by
    intro y hy
    refine (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)
    intro hev
    have hev' : δ =ᶠ[𝓝 y] 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD
      by_contra hz0
      exact hz ⟨hzD, hz0⟩
    have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'
    apply hδne
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz
  exact Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
