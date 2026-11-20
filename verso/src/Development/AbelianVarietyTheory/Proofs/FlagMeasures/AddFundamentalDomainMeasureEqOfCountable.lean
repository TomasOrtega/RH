import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem addFundamentalDomains_measure_eq : ∀ {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (L : Submodule ℤ V) [Countable L] (D D' : Set V), MeasurableSet D → MeasurableSet D' → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D') → μ D = μ D' := by
  intro V _ _ _ μ _ L _ D D' hD hD' hu hu'
  let G : AddSubgroup V := L.toAddSubgroup
  haveI : Countable G := inferInstanceAs (Countable L)
  have key : ∀ E : Set V, MeasurableSet E → (∀ v, ∃! l, l ∈ L ∧ v + l ∈ E) →
      IsAddFundamentalDomain G E μ := by
    intro E hE hEu
    refine IsAddFundamentalDomain.mk' hE.nullMeasurableSet ?_
    intro x
    obtain ⟨l, ⟨hlL, hlE⟩, huniq⟩ := hEu x
    refine ⟨⟨l, hlL⟩, ?_, ?_⟩
    · show (l : V) + x ∈ E
      rwa [add_comm]
    · rintro ⟨g, hg⟩ hgE
      have hgE' : x + g ∈ E := by
        have : (g : V) + x ∈ E := hgE
        rwa [add_comm]
      exact Subtype.ext (huniq g ⟨hg, hgE'⟩)
  exact (key D hD hu).measure_eq (key D' hD' hu')

end GlobalTheory
