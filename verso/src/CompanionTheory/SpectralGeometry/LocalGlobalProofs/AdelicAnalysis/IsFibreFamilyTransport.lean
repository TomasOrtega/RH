import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isFibreFamily_transport :
    ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (V' : Type) [TopologicalSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V'] [T2Space V'] [MeasurableSpace V'] [BorelSpace V'] (f' : V' → Y) (g' : V' → X), Continuous g' → (∀ v, f' v = ι (g' v)) → ∀ (e : V ≃ₜ V') (τ : X ≃ₜ X), (∀ v, g' (e v) = τ (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (μ.map e) f' ι (g' ⁻¹' (τ '' B)) (ν.map τ) (τ '' B) (fun b => (fib (τ.symm b)).map e) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf V' _ _ _ _ _ _ f' g' hg' hf' e τ hc B hB fib h
  obtain ⟨h1, h2, h3⟩ := h
  have hU : e ⁻¹' (g' ⁻¹' (τ '' B)) = g ⁻¹' B := by
    ext v
    simp only [Set.mem_preimage, hc v, τ.injective.mem_set_image]
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hτ : MeasurableEmbedding τ := τ.measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hset : e ⁻¹' (f' ⁻¹' {ι b} ∩ g' ⁻¹' (τ '' B))ᶜ = (f ⁻¹' {ι (τ.symm b)} ∩ g ⁻¹' B)ᶜ := by
      rw [Set.preimage_compl, Set.preimage_inter, hU]
      congr 2
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf, hf', hι.eq_iff, hc v]
      exact ⟨fun hh => by rw [← hh, τ.symm_apply_apply], fun hh => by rw [hh, τ.apply_symm_apply]⟩
    show ((fib (τ.symm b)).map e) _ = 0
    rw [hemb.map_apply, hset]
    exact h1 _
  · intro φ hφ
    have hr : (μ.map e).restrict (g' ⁻¹' (τ '' B)) = (μ.restrict (g ⁻¹' B)).map e := by
      rw [← hU]
      exact (hemb.restrict_map μ _)
    rw [hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable), hτ.lintegral_map]
    refine lintegral_congr fun b => ?_
    simp only [τ.symm_apply_apply, hemb.lintegral_map, Function.comp]
  · intro φ hφ hcs hts
    have hts' : tsupport (φ ∘ e) ⊆ g ⁻¹' B := by
      rw [tsupport_comp_eq_preimage, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨hi, hcont⟩ := h3 (φ ∘ e) (hφ.comp e.continuous)
      (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'
    have hm : Set.MapsTo τ.symm (τ '' B) B := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using hx
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hemb.integrable_map_iff]
      exact hi _ (hm hb)
    · have : (fun b => ∫ v, φ v ∂((fib (τ.symm b)).map e))
          = (fun b => ∫ v, (φ ∘ e) v ∂(fib b)) ∘ τ.symm := by
        funext b
        exact hemb.integral_map φ
      rw [this]
      exact hcont.comp τ.symm.continuous.continuousOn hm

end GlobalTheory.CompanionTheory.SW
