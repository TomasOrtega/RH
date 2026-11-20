import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ClosedSubgroupsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS.Mult1

/- English proof (translation)
Introduce `k r U μ ν hU hμ hν`. Use `haveI : Fact (Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) := ⟨hU⟩`. Take `⟨hμs, hμ0, hμc, hμl⟩` from `hμ`. Take `⟨hνs, hν0, hνc, hνl⟩` from `hν`. Establish `hμc' : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0` using `hμc`.

Establish `hνc' : ν (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0` using `hνc`. Use `haveI := hμs`. Use `haveI := hνs`. Use `haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ`. Use `haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) ν`.

Use `haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap μ hμc' hμl`. Use `haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap ν hνc' hνl`. Establish `hμ0' : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0`. Introduce `h`. Apply `hμ0` to reduce the goal to its premises.

Rewrite using `[← HaarSigmaFiniteUniqueness.map_comap_val μ hμc', h, Measure.map_zero]`. Establish `hν0' : ν.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0`. Introduce `h`. Apply `hν0` to reduce the goal to its premises. Rewrite using `[← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', h, Measure.map_zero]`.

Take `⟨c, hc, hcE⟩` from `HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hν0' hμ0'`. Use `⟨c, pos_iff_ne_zero.mpr hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', hcE, Measure.map_smul, HaarSigmaFiniteUniqueness.map_comap_val μ hμc']`.
-/
theorem haarUniq2 : HaarUniq2Statement := by
  intro k r U μ ν hU hμ hν
  haveI : Fact (Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hμs, hμ0, hμc, hμl⟩ := hμ
  obtain ⟨hνs, hν0, hνc, hνl⟩ := hν
  have hμc' : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hμc
  have hνc' : ν (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hνc
  haveI := hμs
  haveI := hνs
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) ν
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap μ hμc' hμl
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap ν hνc' hνl
  have hμ0' : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hμ0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val μ hμc', h, Measure.map_zero]
  have hν0' : ν.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hν0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', h, Measure.map_zero]
  obtain ⟨c, hc, hcE⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hν0' hμ0'
  refine ⟨c, pos_iff_ne_zero.mpr hc, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', hcE, Measure.map_smul, HaarSigmaFiniteUniqueness.map_comap_val μ hμc']

end ReciprocityTheory.ChartRestriction.DS.Lap
