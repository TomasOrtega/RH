import Mathlib

namespace GlobalTheory

open Topology Filter

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem exists_uniform_preimage_bound_of_isCompact :
    ∀ (T V U : Type) [TopologicalSpace T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (S : Set T), IsCompact S →
    ∀ L : T → V →ₗ[ℝ] U, (∀ v, ContinuousOn (fun t => L t v) S) → (∀ t ∈ S, Function.Surjective (L t)) →
      ∃ C : ℝ, ∀ t ∈ S, ∀ u, ∃ v, L t v = u ∧ ‖v‖ ≤ C * ‖u‖ := by
  intro T V U _ _ _ _ _ _ _ S hS L hc hs
  refine hS.induction_on (p := fun K => ∃ C : ℝ, ∀ t ∈ K, ∀ u, ∃ v, L t v = u ∧ ‖v‖ ≤ C * ‖u‖)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨C, hC⟩
    exact ⟨C, fun x hx => hC x (hst hx)⟩
  · rintro s t ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨max C D, ?_⟩
    rintro x (hx | hx) u
    · obtain ⟨v, h1, h2⟩ := hC x hx u
      exact ⟨v, h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
    · obtain ⟨v, h1, h2⟩ := hD x hx u
      exact ⟨v, h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩
  · intro t₀ ht₀
    obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective (L t₀)
      (LinearMap.range_eq_top.2 (hs t₀ ht₀))
    let A : T → U →L[ℝ] U := fun t => LinearMap.toContinuousLinearMap (L t ∘ₗ R)
    have hA : ∀ t w, A t w = L t (R w) := fun t w => rfl
    have hAc : ContinuousOn A S := by
      rw [continuousOn_clm_apply]
      intro w
      exact hc (R w)
    have hA0 : A t₀ = ContinuousLinearMap.id ℝ U := by
      ext w
      have := LinearMap.congr_fun hR w
      simpa [hA] using this
    have hev : ∀ᶠ t in 𝓝[S] t₀, dist (A t) (A t₀) < 1 / 2 :=
      Metric.tendsto_nhds.1 (hAc t₀ ht₀) (1 / 2) (by norm_num)
    refine ⟨_, hev, 2 * ‖LinearMap.toContinuousLinearMap R‖, ?_⟩
    intro t ht u
    have ht' : ‖A t - ContinuousLinearMap.id ℝ U‖ < 1 / 2 := by
      have : dist (A t) (A t₀) < 1 / 2 := ht
      rwa [hA0, dist_eq_norm] at this
    have hlow : ∀ w, ‖w‖ ≤ 2 * ‖A t w‖ := by
      intro w
      have h1 : ‖A t w - w‖ ≤ 1 / 2 * ‖w‖ := by
        have := (A t - ContinuousLinearMap.id ℝ U).le_opNorm w
        have h2 : (A t - ContinuousLinearMap.id ℝ U) w = A t w - w := rfl
        rw [h2] at this
        exact this.trans (mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _))
      have h3 : ‖w‖ ≤ ‖A t w‖ + ‖A t w - w‖ := by
        have := norm_sub_le (A t w) (A t w - w)
        simpa using this
      linarith
    have hinj : Function.Injective (L t ∘ₗ R) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have h := hlow w
      have h0 : A t w = 0 := hw
      rw [h0, norm_zero, mul_zero] at h
      exact norm_le_zero_iff.1 h
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 hinj u
    have hw' : A t w = u := hw
    refine ⟨R w, hw, ?_⟩
    have h1 : ‖R w‖ ≤ ‖LinearMap.toContinuousLinearMap R‖ * ‖w‖ :=
      (LinearMap.toContinuousLinearMap R).le_opNorm w
    have h2 := hlow w
    rw [hw'] at h2
    calc ‖R w‖ ≤ ‖LinearMap.toContinuousLinearMap R‖ * (2 * ‖u‖) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = _ := by ring

end GlobalTheory
