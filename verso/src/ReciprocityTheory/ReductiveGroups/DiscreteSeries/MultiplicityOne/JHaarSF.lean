import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA

open MeasureTheory
open scoped NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def HaarUniqueSF : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ₀ μ : Measure (Mt k r)), IsClosedSubgroup U → Formalism.FourierDecayAlt.B.IsHaarOn U μ₀ →
    Formalism.MainNotions.S.IsHaarOn U μ → ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • μ₀

/- English proof (translation)
Introduce `k r U μ₀ μ hU h₀ hμ`. Establish `: Fact (IsClosedSubgroup U)` using `⟨hU⟩`. Take `⟨hσ, hne, hconc, hleft⟩` from `hμ`. Establish `: IsFiniteMeasureOnCompacts μ₀` using `⟨h₀.finite_compact⟩`. Establish `hcμ : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0` using `hconc`.

Establish `hcν : μ₀ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0` using `h₀.conc`. Use `HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ` as an intermediate fact. Use `HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ₀` as an intermediate fact. Use `HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ hcμ hleft` as an intermediate fact. Use `HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ₀ hcν h₀.left` as an intermediate fact.

Establish `hμS : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0` using `fun h0 => hne (by`. Rewrite using `[← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, h0, Measure.map_zero])`. Establish `hνS : μ₀.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0` using `fun h0 => h₀.ne_zero (by`. Rewrite using `[← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν, h0, Measure.map_zero])`. Take `⟨c, hc0, hc⟩` from `HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hμS hνS`.

Use `⟨c, hc0, ?_⟩` and prove the remaining obligations. Rewrite using `[← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, hc, Measure.map_smul, HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν]`.
-/
theorem haarUniqueSF' : HaarUniqueSF := by
  intro k r U μ₀ μ hU h₀ hμ
  have : Fact (IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hσ, hne, hconc, hleft⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨h₀.finite_compact⟩
  have hcμ : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hconc
  have hcν : μ₀ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := h₀.conc
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ₀
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ hcμ hleft
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ₀ hcν h₀.left
  have hμS : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => hne (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, h0, Measure.map_zero])
  have hνS : μ₀.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => h₀.ne_zero (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν, h0, Measure.map_zero])
  obtain ⟨c, hc0, hc⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hμS hνS
  refine ⟨c, hc0, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hcμ, hc, Measure.map_smul,
    HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ hcν]

/- English proof (translation)
The claim follows from `haarUniqueSF'`.
-/
theorem haarUniqueSF (_h : UnitaryGroupStructuralFacts) : HaarUniqueSF := haarUniqueSF'

end ReciprocityTheory.ChartRestriction.DS.Mult1
