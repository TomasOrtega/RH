import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TransportSD

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_map_equiv_left {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · have hg' : ¬ AEMeasurable (g ∘ e) μ := by rwa [← aemeasurable_map_equiv_iff e]
    rw [Measure.map_of_not_aemeasurable hg, Measure.map_of_not_aemeasurable hg']

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_map_equiv_right {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) : (μ.map T).map e = μ.map (e ∘ T) := by
  by_cases hT : AEMeasurable T μ
  · exact AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hT
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro h
      apply hT
      have := e.symm.measurable.comp_aemeasurable h
      simpa [Function.comp_def] using this
    rw [Measure.map_of_not_aemeasurable hT, Measure.map_of_not_aemeasurable hT', Measure.map_zero]

end GlobalTheory.TransportSD

open GlobalTheory.TransportSD in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem GlobalTheory.transport_selfDual_fourB : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), (SelfDual μ B → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  let he : V ≃ₜ V' := { toEquiv := h.symm.toEquiv, continuous_toFun := hs, continuous_invFun := hc }
  let e : V ≃ᵐ V' := he.toMeasurableEquiv
  have he_eq : (e : V → V') = h.symm := rfl
  have hμ : Measure.map h.symm μ = Measure.map e μ := by rw [he_eq]
  have four : ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
    intro f y
    unfold fourB
    rw [hμ, integral_map_equiv]
    congr 1
    funext v
    rw [he_eq]
    simp
  refine ⟨fun hsd => ⟨?_, ?_⟩, four⟩
  · obtain ⟨hH, -⟩ := hsd
    rw [hμ]
    have h1 : IsFiniteMeasureOnCompacts (Measure.map e μ) := by
      refine ⟨fun K hK => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have : (e : V → V') ⁻¹' K = h '' K := by
        ext v; rw [he_eq]; simp [Set.mem_image]
        constructor
        · intro hv; exact ⟨h.symm v, hv, by simp⟩
        · rintro ⟨w, hw, rfl⟩; simpa using hw
      rw [this]
      exact (hK.image hc).measure_lt_top
    have h2 : (Measure.map e μ).IsAddLeftInvariant := by
      refine ⟨fun x' => ?_⟩
      rw [map_map_equiv_left]
      have hcomp : (fun y' => x' + y') ∘ (e : V → V') = (e : V → V') ∘ (fun v => h x' + v) := by
        funext v; rw [he_eq]; simp
      rw [hcomp, ← map_map_equiv_right, hH.toIsAddLeftInvariant.map_add_left_eq_self (h x')]
    have h3 : (Measure.map e μ).IsOpenPosMeasure := by
      refine ⟨fun U hU hne => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have hU' : IsOpen ((e : V → V') ⁻¹' U) := hU.preimage (by rw [he_eq]; exact hs)
      have hne' : ((e : V → V') ⁻¹' U).Nonempty := by
        obtain ⟨u, hu⟩ := hne
        exact ⟨h u, by rw [he_eq]; simpa using hu⟩
      exact hU'.measure_ne_zero μ hne'
    exact { toIsFiniteMeasureOnCompacts := h1, toIsAddLeftInvariant := h2, toIsOpenPosMeasure := h3 }
  · intro f hf y
    have hf' : IsTest (fun v => f (h.symm v)) :=
      ⟨hf.1.comp_continuous hs, hf.2.comp_homeomorph he⟩
    rw [four]
    have : (fun v => fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f (h.symm v)) =
        fourB μ B (fun v => f (h.symm v)) := by
      funext v; rw [four]; simp
    rw [this, hsd.2 _ hf' (h y)]
    simp
