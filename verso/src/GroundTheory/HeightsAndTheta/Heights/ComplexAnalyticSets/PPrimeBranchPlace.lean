import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchDimOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveBranchOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Introduce `n J q c hJ hdim`. Establish `hdim1` using `hD n J q c hJ hdim`. Take `⟨M⟩` from `IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ`. Take `⟨Γ, hΓd, hΓ, -⟩` from `hL n 1 J q M c hJ hdim1`. Establish `hr` using `c.radius_pos`.

Establish `h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 c.radius` using `Metric.mem_ball_self hr`. Establish `hinj : Set.InjOn Γ (Metric.ball 0 c.radius)` using `fun a ha b hb hab ↦ c.injOn ha hb (by rw [← (hΓ a ha).2, ← (hΓ b hb).2, hab])`. Take `⟨P, hP⟩` from `hA n J q M (Γ 0) hJ (hΓ 0 h0).1 ((hΓ 0 h0).2.trans c.map_zero)`. Use `⟨P, fun f ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hP f, hO n J M (Γ 0) c.radius Γ hJ hdim1 hr hΓd hinj (fun τ hτ ↦ (hΓ τ hτ).1) rfl]`.

Unfold `branchOrder`. Apply `analyticOrderAt_congr` to reduce the goal to its premises. Use `filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ`. Establish `hτ' : (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius`. Rewrite `hτ`, the goal using `[mem_ball_zero_iff]`.

Conclude with `(pi_norm_const_le τ).trans_lt hτ`. Rewrite using `[eval_rename, ← (hΓ _ hτ').2]`. Both sides reduce to the same expression.
-/
theorem PrimeBranchPlace.proof (hD : PrimeBranchDimOne.Statement) (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement)
    (hA : NormalModelPlace.Statement) (hO : NormalCurveBranchOrder.Statement) : PrimeBranchPlace.Statement := by
  intro n J q c hJ hdim
  have hdim1 := hD n J q c hJ hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n 1 J q M c hJ hdim1
  have hr := c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 c.radius := Metric.mem_ball_self hr

  have hinj : Set.InjOn Γ (Metric.ball 0 c.radius) := fun a ha b hb hab ↦
    c.injOn ha hb (by rw [← (hΓ a ha).2, ← (hΓ b hb).2, hab])
  obtain ⟨P, hP⟩ := hA n J q M (Γ 0) hJ (hΓ 0 h0).1 ((hΓ 0 h0).2.trans c.map_zero)
  refine ⟨P, fun f ↦ ?_⟩
  rw [hP f, hO n J M (Γ 0) c.radius Γ hJ hdim1 hr hΓd hinj (fun τ hτ ↦ (hΓ τ hτ).1) rfl]

  unfold branchOrder
  apply analyticOrderAt_congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
  have hτ' : (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    rw [mem_ball_zero_iff] at hτ ⊢
    exact (pi_norm_const_le τ).trans_lt hτ
  rw [eval_rename, ← (hΓ _ hτ').2]
  rfl

end GroundTheory.Heights₂.Heights
