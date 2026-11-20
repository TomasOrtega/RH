import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountLocallyConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ Y d A D δ hD hDc hmap hprop hδ hsec`. Distinguish the cases in `hne : ∃ y ∈ D, δ y ≠ 0`. Use `swap`. Use `push Not at hne`. Conclude with `⟨0, fun y hy hy' => absurd (hne y hy) hy'⟩`.

Take `⟨y₀, hy₀D, hy₀⟩` from `hne`. Establish `hreg : ∀ y ∈ D, IsRegularPointOf D y` using `fun y hy => ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩`. Establish `hS : IsPreconnected (D \ {z | δ z = 0})` using `hconn (Fin d) D δ hDc hreg hδ ⟨y₀, hy₀D, hy₀⟩`. Establish `hL` using `hloc σ Y d A D δ hD hmap hprop hsec`. Set `f : (Fin d → ℂ) → ℕ` to `fun y => {x | x ∈ Y ∧ A x = y}.ncard`.

Establish `hcont : ContinuousOn f (D \ {z | δ z = 0})`. Introduce `y hy`. Use `ContinuousAt.continuousWithinAt ((continuousAt_const (y := f y)).congr ?_)` and prove the remaining obligations. Use `filter_upwards [(hL y hy.1 hy.2).2] with y' hy'`. Simplify using `only [f, Set.ncard_def, hy']`.

Use `⟨f y₀, fun y hy hyδ => ?_⟩` and prove the remaining obligations. Rewrite using `[← (hL y hy hyδ).1.cast_ncard_eq]`. Conclude with `congrArg _ (hS.constant hcont ⟨hy, hyδ⟩ ⟨hy₀D, hy₀⟩)`.
-/
theorem UnbranchedProperCountConstant.proof (hloc : UnbranchedProperCountLocallyConstant.Statement)
    (hconn : ManifoldZerosComplementConnected.Statement) : UnbranchedProperCountConstant.Statement := by
  intro σ _ Y d A D δ hD hDc hmap hprop hδ hsec
  by_cases hne : ∃ y ∈ D, δ y ≠ 0
  swap
  · push Not at hne
    exact ⟨0, fun y hy hy' => absurd (hne y hy) hy'⟩
  obtain ⟨y₀, hy₀D, hy₀⟩ := hne
  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩
  have hS : IsPreconnected (D \ {z | δ z = 0}) := hconn (Fin d) D δ hDc hreg hδ ⟨y₀, hy₀D, hy₀⟩
  have hL := hloc σ Y d A D δ hD hmap hprop hsec
  let f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Y ∧ A x = y}.ncard
  have hcont : ContinuousOn f (D \ {z | δ z = 0}) := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ((continuousAt_const (y := f y)).congr ?_)
    filter_upwards [(hL y hy.1 hy.2).2] with y' hy'
    simp only [f, Set.ncard_def, hy']
  refine ⟨f y₀, fun y hy hyδ => ?_⟩
  rw [← (hL y hy hyδ).1.cast_ncard_eq]
  exact congrArg _ (hS.constant hcont ⟨hy, hyδ⟩ ⟨hy₀D, hy₀⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
