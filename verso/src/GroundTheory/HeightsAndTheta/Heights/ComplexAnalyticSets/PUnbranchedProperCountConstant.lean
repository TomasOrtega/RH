import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountLocallyConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
