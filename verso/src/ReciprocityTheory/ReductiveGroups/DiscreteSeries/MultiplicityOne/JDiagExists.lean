import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isHaarOn_smul_of {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) : IsHaarOn U (c • μ) where
  conc := by simp [hμ.conc]
  left a ha := by rw [Measure.map_smul, hμ.left a ha]
  right a ha := by rw [Measure.map_smul, hμ.right a ha]
  finite_compact K hK := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hct) (hμ.finite_compact K hK)
  ne_zero := by
    intro h0
    apply hμ.ne_zero
    ext s _
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν s) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero] at h1
    simpa [hc0] using h1

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stDiagExists (h : UnitaryGroupStructuralFacts) : StDiagExists := by
  unfold StDiagExists
  intro k r Wp _ _ _ z π hk hz hT hrep hun hcont hirr
  unfold UnitaryGroupStructuralFacts at h
  obtain ⟨hB2, hBS, -⟩ := h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -⟩ := hB2
  obtain ⟨D, hDz, hDz', hDπ, hDπ', -⟩ :=
    hBS k r Wp Wp z z π π hk hz hz hT hT hrep hrep hun hun hcont hcont
  have hcomp : IsCompact (UWset k r z) := hCW k r z hz hT
  have hW : IsHaarOn (UWset k r z) D.μW := by
    have h0 := D.haarW
    rw [hDz] at h0
    exact h0
  have hm0 : D.μW Set.univ ≠ 0 := by
    intro h0
    exact hW.ne_zero (Measure.measure_univ_eq_zero.mp h0)
  have hmt : D.μW Set.univ ≠ ∞ := by
    have h1 : D.μW Set.univ ≤ D.μW (UWset k r z) + D.μW (UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    rw [hW.conc, add_zero] at h1
    exact ne_top_of_le_ne_top (hW.finite_compact _ hcomp).ne h1
  have hc0 : (D.μW Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmt
  have hct : (D.μW Set.univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm0
  have hH : IsHaarOn (UWset k r D.z) ((D.μW Set.univ)⁻¹ • D.μW) :=
    isHaarOn_smul_of D.haarW hc0 hct
  have hH' : IsHaarOn (UWset k r D.z') ((D.μW Set.univ)⁻¹ • D.μW) := by
    rw [hDz', ← hDz]
    exact hH
  let D' : RealPlaceData k r Wp Wp :=
    { D with
      μW := (D.μW Set.univ)⁻¹ • D.μW
      μW' := (D.μW Set.univ)⁻¹ • D.μW
      haarW := hH
      haarW' := hH' }
  refine ⟨D', hDz, hDπ, ?_⟩
  refine ⟨hDz'.trans hDz.symm, hDπ'.trans hDπ.symm, rfl, ?_, ?_⟩
  · show ((D.μW Set.univ)⁻¹ • D.μW) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm0 hmt]
  · show Formalism.MainNotions.S.IsIrredOn (UWset k r D.z) D.π
    rw [hDz, hDπ]
    exact hirr

end ReciprocityTheory.ChartRestriction.DS.Mult1
