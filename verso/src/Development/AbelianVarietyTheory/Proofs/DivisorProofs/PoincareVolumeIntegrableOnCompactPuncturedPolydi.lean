import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDiscStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Take `⟨R, hR⟩` from `hK.isBounded.exists_norm_le`. Set `g : Fin n → ℂ → ℝ` to `fun a => if a ∈ S then (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) else (Metric.closedBall (0 : ℂ) R).indicator (fun _ => 1)`. Establish `hg : ∀ a, Integrable (g a)`. Introduce `a`. Distinguish the cases in `h : a ∈ S`.

Simplify using `only [g, h, if_true]`. Conclude with `(integrable_indicator_iff measurableSet_closedBall).2 GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc`. Simplify using `only [g, h, if_false]`. Conclude with `(integrable_indicator_iff measurableSet_closedBall).2 (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))`. Establish `h1 : Integrable (fun x : Fin n → ℂ => ∏ a, g a (x a))` using `Integrable.fintype_prod hg`.

Establish `h2` using `(GlobalTheory.volume_preserving_ofLp_complex (Fin n)).integrable_comp_of_integrable h1`. Use `(h2.integrableOn (s := K)).congr_fun ?_ hK.measurableSet` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Function.comp]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : a ∈ S`. Establish `: v.ofLp a ∈ Metric.closedBall (0 : ℂ) (1 / 2)`. Simplify using `using hS v hv a h`. Simplify using `only [g, h, if_true, poinWt]`. Conclude with `Set.indicator_of_mem this _`.

Establish `: v.ofLp a ∈ Metric.closedBall (0 : ℂ) R`. Simplify using `using (PiLp.norm_apply_le v a).trans (hR v hv)`. Simplify using `only [g, h, if_false, poinWt, inv_one, one_pow]`. Conclude with `Set.indicator_of_mem this _`.
-/
theorem integrableOn_poinVol {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)) (hK : IsCompact K)
    (hS : ∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) :
    IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let g : Fin n → ℂ → ℝ := fun a =>
    if a ∈ S then (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2)
    else (Metric.closedBall (0 : ℂ) R).indicator (fun _ => 1)
  have hg : ∀ a, Integrable (g a) := by
    intro a
    by_cases h : a ∈ S
    · simp only [g, h, if_true]
      exact (integrable_indicator_iff measurableSet_closedBall).2 GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc
    · simp only [g, h, if_false]
      exact (integrable_indicator_iff measurableSet_closedBall).2
        (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))
  have h1 : Integrable (fun x : Fin n → ℂ => ∏ a, g a (x a)) := Integrable.fintype_prod hg
  have h2 := (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).integrable_comp_of_integrable h1
  refine (h2.integrableOn (s := K)).congr_fun ?_ hK.measurableSet
  intro v hv
  simp only [Function.comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h : a ∈ S
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      simpa using hS v hv a h
    simp only [g, h, if_true, poinWt]
    exact Set.indicator_of_mem this _
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using (PiLp.norm_apply_le v a).trans (hR v hv)
    simp only [g, h, if_false, poinWt, inv_one, one_pow]
    exact Set.indicator_of_mem this _

end GlobalTheory.GoodTop
