import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.KFock

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem volume_isAddHaar (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  have h2 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : SigmaFinite (volume : Measure (Fin n → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

variable {G H K : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem measure_split (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ c : NNReal, 0 < c ∧ ν = c • Measure.map Φ (la.prod mu) := by
  have hmap : (Measure.map Φ (la.prod mu)).IsAddHaarMeasure :=
    Φ.toAddEquiv.isAddHaarMeasure_map (la.prod mu) Φ.continuous Φ.symm.continuous
  refine ⟨Measure.addHaarScalarFactor ν (Measure.map Φ (la.prod mu)),
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul ν _

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Prove the first alternative. A detailed English derivation is pending.
-/
theorem integral_split (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G → ℂ, ∫ x, g x ∂ν = C * ∫ p, g (Φ p) ∂(la.prod mu) := by
  obtain ⟨c, hc, hν⟩ := measure_split ν la mu Φ
  refine ⟨c, by exact_mod_cast hc, fun g => ?_⟩
  have hm := integral_map_equiv (μ := la.prod mu) (Φ.toHomeomorph.toMeasurableEquiv) g
  rw [hν, integral_smul_nnreal_measure]
  erw [hm]
  simp [NNReal.smul_def, Complex.real_smul]
  exact Or.inl rfl

end PositivityTheory.SiegelWeilFormula.KFock

end
