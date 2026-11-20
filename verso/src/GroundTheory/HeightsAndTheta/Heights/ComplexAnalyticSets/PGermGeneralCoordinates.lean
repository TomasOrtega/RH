import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermGeneralCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_lastCoord_ne_zero_of_mem_nhds {σ : Type} {U : Set (Option σ → ℂ)} {w : Option σ → ℂ}
    (hU : U ∈ 𝓝 w) : ∃ v ∈ U, v none ≠ 0 := by
  classical
  let g : ℂ → Option σ → ℂ := fun s => Function.update w none s
  have hg : Continuous g := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => simpa [g] using continuous_id'
    | some i => simpa [g] using continuous_const
  have hgw : g (w none) = w := Function.update_eq_self none w
  have hev : ∀ᶠ s in 𝓝 (w none), g s ∈ U := by
    have := hg.tendsto (w none)
    rw [hgw] at this
    exact this hU
  have hne : ∀ᶠ s in 𝓝[≠] (w none), s ≠ 0 := by
    by_cases h0 : w none = 0
    · rw [h0]; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)
  obtain ⟨s, hs1, hs2⟩ := (((hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ s in 𝓝[≠] (w none), g s ∈ U).and hne).exists
  exact ⟨g s, hs1, by simpa [g] using hs2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Split into cases according to the possible forms of the given data. Treat this case separately.

Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GeneralLinearCoordinates.proof : GeneralLinearCoordinates.Statement := by
  classical
  intro σ _ f hf hnz
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd

  obtain ⟨w, hwb, hfw⟩ : ∃ w ∈ Metric.ball (0 : Option σ → ℂ) r, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun x hx => h x hx)
  have hUopen : IsOpen (Metric.ball (0 : Option σ → ℂ) r ∩ f ⁻¹' {z | z ≠ 0}) :=
    hfr.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  obtain ⟨v, ⟨hvb, hfv⟩, hvt⟩ := exists_lastCoord_ne_zero_of_mem_nhds (hUopen.mem_nhds ⟨hwb, hfw⟩)
  replace hfv : f v ≠ 0 := hfv

  let e : Option σ → ℂ := Pi.single none 1
  let L : (Option σ → ℂ) →ₗ[ℂ] (Option σ → ℂ) :=
    LinearMap.id + (LinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).smulRight (v - e)
  have hL : ∀ x, L x = x + x none • (v - e) := fun x => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (L x) none = 0 := by rw [hx]; rfl
    have hnone : x none = 0 := by
      rw [hL] at h1
      simp [e] at h1
      have h2 : x none * v none = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hvt
    rw [hL, hnone, zero_smul, add_zero] at hx
    exact hx
  let A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ) :=
    (LinearEquiv.ofInjectiveEndo L hLinj).toContinuousLinearEquiv
  have hA : ∀ t : ℂ, A (pointWithLast 0 t) = t • v := by
    intro t
    show L (pointWithLast 0 t) = t • v
    rw [hL]
    funext o
    cases o with
    | none => simp [pointWithLast, e]; ring
    | some i => simp [pointWithLast, e]
  refine ⟨A, ?_⟩
  have hfun : (fun t => f (A (pointWithLast 0 t))) = fun t : ℂ => f (t • v) := by
    funext t; rw [hA]
  rw [hfun]

  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr fun h => hvt (by rw [h]; rfl)
  have hvr : ‖v‖ < r := by simpa using hvb
  set R := r / ‖v‖
  have hR1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact (one_lt_div hv0).mpr hvr
  have hR0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (lt_trans one_pos
    ((one_lt_div hv0).mpr hvr))
  have han : AnalyticOnNhd ℂ (fun t : ℂ => f (t • v)) (Metric.ball (0 : ℂ) R) := by
    intro t ht
    have htv : t • v ∈ Metric.ball (0 : Option σ → ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      rw [Metric.mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖v‖ < R * ‖v‖ := mul_lt_mul_of_pos_right ht hv0
        _ = r := div_mul_cancel₀ r hv0.ne'
    have hs : AnalyticAt ℂ (fun s : ℂ => s • v) t := analyticAt_id.smul analyticAt_const
    show AnalyticAt ℂ (f ∘ fun s : ℂ => s • v) t
    exact AnalyticAt.comp (f := fun s : ℂ => s • v) (x := t) (hfr _ htv) hs
  have hnot : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), f (t • v) = 0) := by
    intro h
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hR0 h hR1
    simp at this
    exact hfv this
  have hne : analyticOrderAt (fun t : ℂ => f (t • v)) 0 ≠ ⊤ := fun h =>
    hnot (analyticOrderAt_eq_top.mp h)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨d, hd.symm⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
